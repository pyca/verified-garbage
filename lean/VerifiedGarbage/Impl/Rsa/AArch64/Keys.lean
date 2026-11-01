module

public import VerifiedGarbage.Impl.Rsa.AArch64.CarrySelect
public import VerifiedGarbage.Impl.Rsa.AArch64.InvBatch
public import VerifiedGarbage.Impl.Rsa.AArch64
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Inv

/-!
# RSA private keys on AArch64: the shared routines and `vg_rsa_crt_values`

x86-64's computation (`Impl/Rsa/X86_64/Keys.lean`), in the same layout:
`vg_rsa_public`'s working space (`Impl/Bignum/Layout.lean`), a header of 32
words and arrays of `w + 2` words after it, array `j` at byte
`256 + 8 (w + 2) j`. The routines here compute every base from `x0` and
the stride `8 (w + 2)` (in `x11`, from the header), with `w` in `x12`:
their addresses and branches depend only on `x0`, `w` and the stride, all
public.

* `divmod q r d t`: the remainder and the quotient of `[q]` by `[d]`
  (`w` words each), by `64 w` steps of bit-serial division: `([r], [q])`
  shifted left a bit, then `[t] = [r] - [d]` over `w + 1` words and `[r]`
  replaced by `[t]` and `[q]`'s low bit set if it does not borrow. `[r]`
  ends as the remainder and `[q]` as the quotient.
* `inverse u v x₁ x₂ m t`: `128 w` steps of the binary extended Euclidean
  algorithm modulo the odd `[m]`: from `([u], [v], [x₁], [x₂]) =
  (a, m, 1, 0)`, `[v]` ends as `gcd(a, m)` and `[x₂]` with
  `[x₂] a ≡ [v] (mod m)`. Each step, under masks from the low bit of `[u]`
  and the borrow of `[u] - [v]`: `(u, v, x₁, x₂)` swapped to
  `(v, u, x₂, x₁)` if `u` is odd and below `v`, then
  `u -= v` and `x₁ -= x₂ (mod m)` if `u` is odd, then `u` and `x₁` halved
  (`x₁ + m` if `x₁` is odd).

A loop walks pointers over the words, as `Impl/Bignum/AArch64.lean`'s do,
counting down `x14` with `cbnz`; carry chains keep their carry in the carry
flag. The step counters of `divmod` and `inverse` are `x6`, which the
steps leave alone, and the odd mask of `inverse`'s `u` is `x9`. The loops
use the registers of `vg_rsa_private_crt`'s (`Impl/Rsa/AArch64/Crt.lean`),
whose proofs they share: a subtraction into `x13`, a masked addition of
`[x10]` and `[x8]` into `x5`, `selLoop`.

`vg_rsa_crt_values(dp, dp_len, dq, dq_len, qinv, qinv_len, n, n_len, p,
p_len, q, q_len, d, d_len, scratch, scratch_len)`: the first eight
arguments in `x0`–`x7`, the others on the stack. `n` is checked as
`vg_rsa_public` checks it (it is public); then `p q = n` gives a mask,
`qInv` is computed by `inverse` (and'ing `gcd(q, p) = 1` into the mask),
and `dP` and `dQ` by `divmod` (with the divisor `p` or `q` with its low bit
cleared: `p - 1` for an odd `p`, which `p q = n` implies). Each result is
written out masked. `p q = n` is checked by `divmod` too, as
`n mod p = 0`, `n / p = q` and `p` odd.
-/

@[expose] public section

namespace VG.Impl.Rsa.AArch64.Keys

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.Public VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64

/-! ## Arrays by their index -/

/-- The header slot of the stride `8 (w + 2)`. -/
def sStride : Nat := sFn 12

/-- `w` into `x12` and the stride into `x11`. -/
def ws : List Instr := [ldh .x12 sW, ldh .x11 sStride]

/-- `x0 + 256 + j · x11` into `r` by `j` additions of `x11`. -/
def baseRep (j : Nat) (r : Reg) : List Instr :=
  ([.addImm .x r .x0 hdrBytes] : List Instr) ++ List.replicate j (.add .x r r .x11)

/-- `mulBits` with `f` bits of fuel (`j ≤ f` suffices), by structural
recursion, which the kernel evaluates. -/
def mulBitsF (r : Reg) : Nat → Nat → List Instr
  | 0, _ => []
  | f + 1, j => if j < 2 then [] else
    mulBitsF r f (j / 2) ++ ([.add .x r r r] : List Instr) ++
      (if j % 2 = 1 then ([.add .x r r .x11] : List Instr) else [])

/-- `r := j · x11` for `j ≥ 1`, from `r = x11`, by the bits of `j` below its
top one, most significant first: `r := 2 r`, then `r := r + x11` if the
bit is set. -/
def mulBits (r : Reg) (j : Nat) : List Instr := mulBitsF r j j

/-- The base of array `j` into `r`: `x0 + 256 + j · x11`, with `j · x11` by
`mulBits` (`r` only; `baseRep` for `j = 0`, or `r = x0`, which reads `x0`
first). -/
def base (j : Nat) (r : Reg) : List Instr :=
  if j = 0 ∨ r = .x0 then baseRep j r
  else ([.addImm .x r .x11 0] : List Instr) ++ mulBits r j ++
    ([.add .x r r .x0, .addImm .x r r hdrBytes] : List Instr)

/-- `[j] := 0` (`w + 2` words). -/
def zeroA (j : Nat) : Prog isa := .seq (.block (ws ++ base j .x8 ++ [movi .x7 0])) zeroAcc

/-- `[o] := [a]` over `w` words. -/
def copyA (o a : Nat) : Prog isa := .seq (.block (ws ++ base a .x16 ++ base o .x17)) copyWords

/-- `x15 :=` all ones if the carry flag is set, 0 otherwise (`x4 := 0 - 1`,
`x7 = 0`). -/
def carryMask : List Instr := [.subImm .x .x4 .x7 1, .csel .x .x15 .x4 .x7]

/-- `x15 :=` all ones if the carry flag is clear (a borrow), 0 otherwise
(`x4 := 0 - 1`, `x7 = 0`). -/
def borrowMask : List Instr := [.subImm .x .x4 .x7 1, .csel .x .x15 .x7 .x4]

/-- `x15 := 0 - (x3 & 1)`: all ones if `x3` is odd (`x4 := 1`, `x7 = 0`). -/
def oddMask : List Instr := [movi .x4 1, .logic .and .x .x3 .x3 .x4, .sub .x .x15 .x7 .x3]

/-! ## Loops over the words -/

/-- `[x16] := 2 [x16] + c` with the carry chain in the carry flag. -/
def shlBody : List Instr := [ld .x3 .x16, .adcs .x .x3 .x3 .x3, st .x3 .x16, next .x16]

/-- `[x13] := [x16] - [x17]` with the borrow chain in the carry flag
(`subMod`'s). -/
def subBody : List Instr :=
  [ld .x3 .x16, ld .x4 .x17, .sbcs .x .x3 .x3 .x4, st .x3 .x13, next .x16, next .x17, next .x13]

/-- `[x8] := [x16] - ([x17] & x15)` with the borrow chain in the carry
flag. -/
def subMBody : List Instr :=
  [ld .x3 .x16, ld .x4 .x17, .logic .and .x .x4 .x4 .x15, .sbcs .x .x3 .x3 .x4, st .x3 .x8, next .x16,
    next .x17, next .x8]

/-- `[x5] := ([x10] & x15) + [x8]` with the carry chain in the carry flag
(`subModArr`'s second loop). -/
def addMBody : List Instr :=
  [ld .x3 .x10, .logic .and .x .x3 .x3 .x15, ld .x4 .x8, .adcs .x .x3 .x3 .x4, st .x3 .x5, next .x10, next .x8,
    next .x5]

/-- `[x17] := [x16] / 2`, word `i` from words `i` and `i + 1` of `[x16]`
(`extr`: the low bit of word `i + 1` as the top bit of word `i`). -/
def shrBody : List Instr :=
  [ld .x3 .x16, ld .x4 .x16 8, .extr .x .x3 .x4 .x3 1, st .x3 .x17, next .x16, next .x17]

/-- `[x16], [x17] := [x17], [x16]` under the mask `x15`. -/
def cswapBody : List Instr :=
  [ld .x3 .x16, ld .x4 .x17, .logic .eor .x .x5 .x3 .x4, .logic .and .x .x5 .x5 .x15,
    .logic .eor .x .x3 .x3 .x5, .logic .eor .x .x4 .x4 .x5, st .x3 .x16, st .x4 .x17, next .x16, next .x17]

/-- `x9 |= [x16] ^ [x17]`. -/
def xorBody : List Instr :=
  [ld .x3 .x16, ld .x4 .x17, .logic .eor .x .x3 .x3 .x4, .logic .orr .x .x9 .x9 .x3, next .x16, next .x17]

/-! ## Division -/

/-- `([r], [q]) := 2 ([r], [q])`, `[r]` over `w + 1` words: one chain of
`adcs` from the carry clear. -/
def divShiftP (iQ iR : Nat) : List (Prog isa) := [
  .block ([movi .x7 0, mov .x14 .x12, .adds .x .x3 .x7 .x7] ++ base iQ .x16),
  countLoop .x14 shlBody,
  .block (base iR .x16 ++ ([.addImm .x .x14 .x12 1] : List Instr)),
  countLoop .x14 shlBody]

/-- `[t] := [r] - [d]` over `w + 1` words (word `w` of `[d]` taken as zero),
then `[r] := [t]` if it does not borrow, `x15` the mask of no borrow. -/
def divSubP (iR iD iT : Nat) : List (Prog isa) := [
  .block ([movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base iR .x16 ++ base iD .x17 ++ base iT .x13),
  countLoop .x14 subBody,
  .block ([ld .x3 .x16, .sbcs .x .x3 .x3 .x7, st .x3 .x13] ++ carryMask ++ base iT .x16 ++ base iR .x17 ++
    ([.addImm .x .x14 .x12 1] : List Instr)),
  CarrySelect.code]

/-- `[q] += 1` if it did not borrow (its low bit is clear after the shift),
and the step counter `x6` counted down. -/
def divBitP (iQ : Nat) : List Instr :=
  base iQ .x16 ++ [ld .x3 .x16, movi .x4 1, .logic .and .x .x4 .x4 .x15, .logic .orr .x .x3 .x3 .x4, st .x3 .x16,
    .subImm .x .x6 .x6 1]

/-- One step of the division. -/
def divStep (iQ iR iD iT : Nat) : Prog isa := seqs (divShiftP iQ iR ++ (divSubP iR iD iT ++ [.block (divBitP iQ)]))

/-- `[r] := 0` and `x6 := 64 w`. -/
def divInit (iR : Nat) : List (Prog isa) := [zeroA iR, .block [.lsl .x .x6 .x12 6]]

/-- `[r] := [q] mod [d]` and `[q] := [q] / [d]`, `[t]` working space:
`64 w` steps. -/
def divmod (iQ iR iD iT : Nat) : Prog isa :=
  seqs (divInit iR ++ [.loop (divStep iQ iR iD iT) (.nonzero .x .x6)])

/-! ## The binary extended Euclidean algorithm -/

/-- The mask of `u` odd into `x9`, the mask of `u < v` and'ed with it into
`x15`, and the swaps of `(u, v)` and `(x₁, x₂)` under it. -/
def invSwapP (iU iV iX₁ iX₂ : Nat) : List (Prog isa) := [
  .block [movi .x7 0, mov .x14 .x12],
  .block (base iU .x16 ++ base iV .x17),
  .block ([ld .x3 .x16] ++ oddMask ++ [mov .x9 .x15, .subs .x .x3 .x7 .x7]),
  cmpLoop,
  .block (borrowMask ++ ([.logic .and .x .x15 .x15 .x9, mov .x14 .x12] : List Instr)),
  .block (base iU .x16 ++ base iV .x17),
  countLoop .x14 cswapBody,
  .block [mov .x14 .x12],
  .block (base iX₁ .x16 ++ base iX₂ .x17),
  countLoop .x14 cswapBody]

/-- `u -= v`, if `u` is odd. -/
def invSubUP (iU iV : Nat) : List (Prog isa) := [
  .block [movi .x7 0, mov .x15 .x9, mov .x14 .x12, .subs .x .x3 .x7 .x7],
  .block (base iU .x16 ++ base iV .x17 ++ base iU .x8),
  countLoop .x14 subMBody]

/-- `x₁ -= x₂ (mod m)`, if `u` is odd: `t := x₁ - (x₂ & x9)`, then
`x₁ := (m & borrow) + t`. -/
def invSubXP (iX₁ iX₂ iM iT : Nat) : List (Prog isa) := [
  .block [mov .x15 .x9, mov .x14 .x12, .subs .x .x3 .x7 .x7],
  .block (base iX₁ .x16 ++ base iX₂ .x17 ++ base iT .x8),
  countLoop .x14 subMBody,
  .block (borrowMask ++ [mov .x14 .x12, .adds .x .x3 .x7 .x7]),
  .block (base iM .x10 ++ base iT .x8 ++ base iX₁ .x5),
  countLoop .x14 addMBody]

/-- `u -= v` and `x₁ -= x₂ (mod m)`, if `u` is odd. -/
def invSubP (iU iV iX₁ iX₂ iM iT : Nat) : List (Prog isa) := invSubUP iU iV ++ invSubXP iX₁ iX₂ iM iT

/-- `u /= 2`. -/
def invHalfUP (iU : Nat) : List (Prog isa) :=
  [.block [mov .x14 .x12], .block (base iU .x16 ++ base iU .x17), countLoop .x14 shrBody]

/-- `x₁ := x₁ / 2 (mod m)`: `t := x₁ + m` if `x₁` is odd (`w + 1` words),
then `x₁ := t / 2`. -/
def invHalfXP (iX₁ iM iT : Nat) : List (Prog isa) := [
  .block (base iX₁ .x8),
  .block ([ld .x3 .x8] ++ oddMask ++ [mov .x14 .x12, .adds .x .x3 .x7 .x7]),
  .block (base iM .x10 ++ base iT .x5),
  countLoop .x14 addMBody,
  .block [.adc .x .x3 .x7 .x7, st .x3 .x5, mov .x14 .x12],
  .block (base iT .x16 ++ base iX₁ .x17),
  countLoop .x14 shrBody]

/-- `u /= 2` and `x₁ := x₁ / 2 (mod m)`. -/
def invHalfP (iU iX₁ iM iT : Nat) : List (Prog isa) := invHalfUP iU ++ invHalfXP iX₁ iM iT

/-- One step of `inverse`, and the step counter `x6` counted down. -/
def invStep (iU iV iX₁ iX₂ iM iT : Nat) : Prog isa :=
  seqs (invSwapP iU iV iX₁ iX₂ ++ (invSubP iU iV iX₁ iX₂ iM iT ++ (invHalfP iU iX₁ iM iT ++
    [.block [.subImm .x .x6 .x6 1]])))

/-- `x6 := 128 w`. -/
def invInit : List Instr := ws ++ ([.lsl .x .x6 .x12 7] : List Instr)

/-- `128 w` steps of the binary extended Euclidean algorithm. -/
def inverseBits (iU iV iX₁ iX₂ iM iT : Nat) : Prog isa :=
  .seq (.block invInit) (.loop (invStep iU iV iX₁ iX₂ iM iT) (.nonzero .x .x6))

/-! ## The batched inverse

`inverse`'s arrays, at the width `n` in `x12` (`n + 1` words of each signed
number, two's complement): `f` in `v`, `g` in `u`, `a` in `x₂`, `b` in `x₁`,
the products in `t`; `m` is read only. `d`, `-m⁻¹ mod 2^64`, the matrix of
a batch and the saved `x1`, `x2` are in the lanes of `v16`–`v19`, which the
caller's convention does not preserve; the public counts stay in registers
(`x15` the batches, `x11` and `x12` packed into `x14` through the
divsteps). -/

open InvBatch

/-- `x14 := n + 1`. -/
def cntL : Instr := .addImm .x .x14 .x12 1

/-- `r := ` the address of word `n` of array `j` (through `x3`). -/
def topAt (j : Nat) (r : Reg) : List Instr := base j r ++ [.lsl .x .x3 .x12 3, .add .x r r .x3]

/-- Word `n` of array `j` := 0. -/
def zeroTop (j : Nat) : List Instr := topAt j .x16 ++ [movi .x3 0, st .x3 .x16]

/-- `x15 :=` the sign mask of word `n` of array `j`, and `x7 := 0`. -/
def signMask (j : Nat) : List Instr :=
  topAt j .x16 ++ [ld .x3 .x16, .lsr .x .x3 .x3 63, movi .x7 0, .sub .x .x15 .x7 .x3]

/-- `[o] := x4 [x] + x5 [y]` modulo `2^(64 (n + 1))`, the coefficients
from the lanes of `cv`. -/
def rowP (cv : VReg) (iX iY iO : Nat) : Prog isa :=
  .seq (.block ([.umov .x .x4 cv 0, .umov .x .x5 cv 1] ++ coefMasks ++ base iX .x16 ++ base iY .x17 ++
      base iO .x8 ++ ([cntL, movi .x13 0] : List Instr)))
    (countLoop .x14 rowBody)

/-- `[o] := [s] >> 59`, `n + 1` words. -/
def shrP (iS iO : Nat) : Prog isa :=
  .seq (.block (base iS .x16 ++ base iO .x17 ++ ([mov .x14 .x12] : List Instr)))
    (.seq (countLoop .x14 shrBody) (.block shrTop))

/-- `[o] := ([a] + k m) / 2^64` for `k = a₀ (-m⁻¹) mod 2^64`, `[a]` of `n + 1`
words sign-extended to `n + 2`. -/
def mredP (iA iM iO : Nat) : List (Prog isa) := [
  .block ([.umov .x .x5 .v18 1] ++ base iA .x8 ++ ([ld .x3 .x8, .mul .x .x1 .x3 .x5, .lsl .x .x6 .x12 3,
    .add .x .x6 .x8 .x6, ld .x3 .x6, .lsr .x .x3 .x3 63, movi .x7 0, .sub .x .x3 .x7 .x3, st .x3 .x6 8] : List Instr) ++
    base iM .x9),
  mulAddRow,
  .block (base iA .x16 ++ ([next .x16] : List Instr) ++ base iO .x17 ++ ([cntL] : List Instr)),
  countLoop .x14 copyBody]

/-- A batch's start: `d` and the low words of `f` and `g`, `59` divsteps,
`d` and the matrix into `v18`, `v16`, `v17`, and the batch counted. -/
def batchHead (iF iG : Nat) : List Instr :=
  base iF .x2 ++ [ld .x2 .x2] ++ base iG .x3 ++ [ld .x3 .x3, .umov .x .x1 .v18 0] ++ packW ++ VG.Impl.Weierstrass.AArch64.pwords ++
  [.vop (.ins .d2 .v18 0 .x1), .vop (.ins .d2 .v16 0 .x4), .vop (.ins .d2 .v16 1 .x5),
    .vop (.ins .d2 .v17 0 .x6), .vop (.ins .d2 .v17 1 .x7)] ++ unpackW ++ [.subImm .x .x15 .x15 1]

/-- A batch: `(f, g) := (u f + v g, q f + r g) / 2^59` and
`(a, b) := (mredRaw (u a + v b), mredRaw (q a + r b))`. -/
def batch (iF iG iA iB iT iM : Nat) : Prog isa := seqs ([
  .block (batchHead iF iG),
  rowP .v16 iF iG iT, rowP .v17 iF iG iG, shrP iT iF, shrP iG iG,
  rowP .v16 iA iB iT, rowP .v17 iA iB iB] ++ mredP iT iM iA ++ mredP iB iM iB)

/-- The start: `x1`, `x2` saved, `f = m` (its word `n` cleared),
`g = a + (m if a is even)`, `a = 0`, `b = 1`, `-m⁻¹` and `d = 1` into
`v18`, and `x15 := 3 n + 2`. -/
def batchInit (iF iG iA iB iM : Nat) : List (Prog isa) := [
  .block ([.vop (.ins .d2 .v19 0 .x1), .vop (.ins .d2 .v19 1 .x2)] ++ zeroTop iF ++ zeroTop iG ++ base iG .x8 ++
    ([ld .x3 .x8, movi .x4 1, .logic .and .x .x3 .x3 .x4, .subImm .x .x15 .x3 1, movi .x7 0, mov .x14 .x12,
      .adds .x .x3 .x7 .x7] : List Instr) ++ base iM .x10 ++ base iG .x5),
  countLoop .x14 addMBody,
  .block [.adc .x .x3 .x7 .x7, st .x3 .x5],
  .seq (.block (base iA .x8 ++ ([movi .x7 0] : List Instr))) zeroAcc,
  .seq (.block (base iB .x8 ++ ([movi .x7 0] : List Instr))) zeroAcc,
  .block (base iB .x16 ++ ([movi .x3 1, st .x3 .x16] : List Instr) ++ base iM .x3 ++ ([ld .x3 .x3] : List Instr) ++
    minv ++ [.vop (.ins .d2 .v18 1 .x15), movi .x3 1, .vop (.ins .d2 .v18 0 .x3)] ++ batchCount)]

/-- `[x] := -[x]` (`n + 1` words) where the mask `x15` is all ones. -/
def cnegP (iX : Nat) : Prog isa :=
  .seq (.block (base iX .x16 ++ ([cntL, movi .x7 0, .adds .x .x3 .x15 .x15] : List Instr))) (countLoop .x14 cnegBody)

/-- `[a] += m` (`n + 1` words, `m`'s word `n` zero) if `[a]` is negative. -/
def addIfNeg (iA iM : Nat) : List (Prog isa) := [
  .block (signMask iA ++ ([mov .x14 .x12, .adds .x .x3 .x7 .x7] : List Instr) ++ base iM .x10 ++ base iA .x8 ++
    base iA .x5),
  countLoop .x14 addMBody,
  .block [ld .x3 .x5, .adc .x .x3 .x3 .x7, st .x3 .x5]]

/-- `[a] := [a] - m` if `[a] ≥ m` (`[a] < 2 m`), through `[t]`, and its word
`n` cleared. -/
def csubP (iA iM iT : Nat) : List (Prog isa) := [
  .block (base iA .x8 ++ base iM .x10 ++ base iT .x6 ++ base iA .x5 ++ ([movi .x7 0] : List Instr)),
  subMod, selectAcc, .block (zeroTop iA)]

/-- `[a] := 2 [a] mod m`, the double in `[t]` and the difference in `[s]`. -/
def dblP (iA iM iT iS : Nat) : Prog isa :=
  .seq (.block (base iA .x5 ++ base iM .x10 ++ base iT .x8 ++ base iS .x6 ++
      ([movi .x7 0, mov .x17 .x5, mov .x16 .x8, mov .x14 .x12, .adds .x .x3 .x7 .x7] : List Instr)))
    (.seq (countLoop .x14 dblBody) (.seq (.block [.adc .x .x3 .x7 .x7, st .x3 .x16]) (.seq subMod selectAcc)))

/-- The end: `v := |f|`, `x₂ := ±a 2^(5 B) mod m` (`B = 3 n + 2`), and `x1`,
`x2` restored. -/
def batchFinish (iF iG iA iM iT : Nat) : List (Prog isa) :=
  [.block (signMask iF), cnegP iF, cnegP iA] ++ addIfNeg iA iM ++ addIfNeg iA iM ++ csubP iA iM iT ++
  [.seq (.block dblCount) (.loop (.seq (dblP iA iM iT iG) (.block [.subImm .x .x15 .x15 1])) (.nonzero .x .x15)),
   .block [.umov .x .x1 .v19 0, .umov .x .x2 .v19 1]]

/-- The batched inverse at the width in `x12`. -/
def inverseB (iU iV iX₁ iX₂ iM iT : Nat) : Prog isa :=
  seqs (batchInit iV iU iX₂ iX₁ iM ++ [.loop (batch iV iU iX₂ iX₁ iT iM) (.nonzero .x .x15)] ++
    batchFinish iV iU iX₂ iM iT)

/-- The inverse at the width in `x12` (`x11` the stride): by batches of
divsteps for a width below `2^21`, else bit by bit at the header's width. -/
def inverseN (iU iV iX₁ iX₂ iM iT : Nat) : Prog isa :=
  .seq (.block [.lsr .x .x3 .x12 21])
    (.ite (.zero .x .x3) (inverseB iU iV iX₁ iX₂ iM iT) (inverseBits iU iV iX₁ iX₂ iM iT))

/-- `inverse u v x₁ x₂ m t`: `[v] = gcd(a, m)` and `[x₂] a ≡ [v] (mod m)`
for `[u] = a` and the odd `[m] = [v]`. -/
def inverse (iU iV iX₁ iX₂ iM iT : Nat) : Prog isa :=
  .seq (.block ws) (inverseN iU iV iX₁ iX₂ iM iT)

/-! ## Masks -/

/-- `x9 = 0` iff `[a] = [b]` over `w` words. -/
def eqA (a b : Nat) : List (Prog isa) :=
  [.block (ws ++ [movi .x9 0, mov .x14 .x12]), .block (base a .x16 ++ base b .x17), countLoop .x14 xorBody]

/-- `[j] := 1`, for `[j] = 0`. -/
def setOneA (j : Nat) : List Instr := ws ++ base j .x16 ++ [movi .x3 1, st .x3 .x16]

/-- The low word of `[j]` minus one (`[j] - 1` for a `[j]` whose low word
is not zero). -/
def decA (j : Nat) : List Instr := ws ++ base j .x16 ++ [ld .x3 .x16, .subImm .x .x3 .x3 1, st .x3 .x16]

/-! ## Bytes -/

/-- `[j] := ` the number of the bytes whose pointer and length are in the
header slots `sPtr` and `sLen`. -/
def loadA (j sPtr sLen : Nat) : List (Prog isa) :=
  [zeroA j, .block (ws ++ base j .x8 ++ [ldh .x1 sPtr, ldh .x2 sLen]), loadBE]

/-- `[j]` masked by the header slot `sMsk`, to the bytes whose pointer and
length are in the header slots `sPtr` and `sLen`. -/
def storeA (j sPtr sLen sMsk : Nat) : List (Prog isa) :=
  [.block (ws ++ base j .x8 ++ [ldh .x1 sPtr, ldh .x9 sLen, .add .x .x1 .x1 .x9, ldh .x15 sMsk]), storeBE]

/-- Zeros to the bytes whose pointer and length are in the header slots
`sPtr` and `sLen` (at least one). -/
def zeroOut (sPtr sLen : Nat) : Prog isa :=
  .seq (.block [ldh .x1 sPtr, ldh .x2 sLen, movi .x3 0]) (countLoop .x2 [.strb .x3 .x1 0, .addImm .x .x1 .x1 1])

/-- The mask's low bit returned. -/
def retMask : List Instr := [ldh .x3 sMask, movi .x4 1, .logic .and .x .x0 .x3 .x4]

/-- The mask of `x9 = 0` and'ed into `sMask`: `x9 - 1` borrows. -/
def andZero : List Instr :=
  [movi .x7 0, movi .x4 1, .subs .x .x3 .x9 .x4] ++ borrowMask ++
    [ldh .x3 sMask, .logic .and .x .x15 .x15 .x3, sth .x15 sMask]

/-- `w`, the arrays' bases and the stride `8 (w + 2)`, and the mask all
ones. -/
def head : List Instr :=
  Rsa.AArch64.head ++ ([.addImm .x .x3 .x12 2, .lsl .x .x3 .x3 3, sth .x3 sStride, movi .x7 0,
    .subImm .x .x4 .x7 1, sth .x4 sMask] : List Instr)

/-! ## `vg_rsa_crt_values` -/

namespace CrtValues

/-- Header slots: `n`'s pointer and length in `vg_rsa_public`'s `sN` and
`sK`, the mask in its `sMask`. -/
def sDp : Nat := sFn 0
def sDq : Nat := sFn 3
def sQi : Nat := sFn 4
def sPl : Nat := sFn 5
def sQl : Nat := sFn 7
def sP : Nat := sFn 8
def sQ : Nat := sFn 9
def sD : Nat := sFn 10
def sDl : Nat := sFn 11

/-- The arrays: `n` (0), `p` (1), `divmod`'s quotient and remainder or
`inverse`'s `u` and `v` (2 and 3), `q` (4), `d` (5), `inverse`'s `x₁` and
`x₂` (6 and 7), the working array (8) and a constant or the divisor (9,
`aC`). -/
def aP : Nat := 1
def aQ : Nat := 4
def aD : Nat := 5
def aU : Nat := 2
def aV : Nat := 3
def aX₁ : Nat := 6
def aX₂ : Nat := 7
def aT : Nat := 8
def aC : Nat := 9

/-- The arguments in the header at `scratch` (the seventh stack argument),
whose base goes in `x0`. `dp_len` and `dq_len` are `p_len` and `q_len`. -/
def entry : List Instr :=
  [.ldrSp .x8 48, .str .x .x0 .x8 (8 * sDp), .str .x .x1 .x8 (8 * sPl), .str .x .x2 .x8 (8 * sDq),
    .str .x .x3 .x8 (8 * sQl), .str .x .x4 .x8 (8 * sQi), .str .x .x6 .x8 (8 * sN), .str .x .x7 .x8 (8 * sK),
    .ldrSp .x9 0, .str .x .x9 .x8 (8 * sP), .ldrSp .x9 16, .str .x .x9 .x8 (8 * sQ),
    .ldrSp .x9 32, .str .x .x9 .x8 (8 * sD), .ldrSp .x9 40, .str .x .x9 .x8 (8 * sDl), mov .x0 .x8,
    mov .x2 .x6, mov .x3 .x7]

/-- Zeros to `dp`, `dq` and `qinv`, and 0 returned. -/
def fail : Prog isa := seqs [zeroOut sDp sPl, zeroOut sDq sQl, zeroOut sQi sPl, .block [movi .x0 0]]

/-- The mask of `[j]` odd and'ed into `sMask`. -/
def andOdd (j : Nat) : List Instr :=
  ws ++ base j .x16 ++ [movi .x7 0, ld .x3 .x16] ++ oddMask ++
    [ldh .x3 sMask, .logic .and .x .x15 .x15 .x3, sth .x15 sMask]

/-- The mask of `p q = n` and'ed into `sMask`, as `n mod p = 0`,
`n / p = q` and `p` odd (which `p q = n` implies, `n` being odd). -/
def pqCheck : List (Prog isa) :=
  [zeroA aU, copyA aU aN, divmod aU aV aP aT] ++ eqA aU aQ ++ [.block andZero, zeroA aC] ++ eqA aV aC ++
    [.block andZero, .block (andOdd aP)]

/-- `inverse`'s start: `(u, v, x₁, x₂) := (q, p, 1, 0)`. -/
def invSetup : List (Prog isa) :=
  [zeroA aU, copyA aU aQ, zeroA aV, copyA aV aP, zeroA aX₁, .block (setOneA aX₁), zeroA aX₂]

/-- `qInv = q⁻¹ mod p` into `aX₂`, and `gcd(q, p) = 1` and'ed into `sMask`. -/
def invPart : List (Prog isa) :=
  invSetup ++ ([inverse aU aV aX₁ aX₂ aP aT, zeroA aC, .block (setOneA aC)] ++ (eqA aV aC ++ [.block andZero]))

/-- `[aC] := [j] - 1` (for an odd `[j]`, whose low word is not zero), then
`[aU] := d`. -/
def divisor (j : Nat) : List (Prog isa) :=
  [zeroA aC, copyA aC j, .block (decA aC), zeroA aU, copyA aU aD]

/-- The computation, once `n` is known valid. -/
def main : Prog isa := seqs ([
  .block head] ++ loadA aN sN sK ++ loadA aP sP sPl ++ loadA aQ sQ sQl ++ loadA aD sD sDl ++ pqCheck ++ invPart ++
  -- `dP = d mod (p - 1)` into `aX₁` and `dQ = d mod (q - 1)` in `aV`.
  divisor aP ++ [divmod aU aV aC aT, zeroA aX₁, copyA aX₁ aV] ++ divisor aQ ++ [divmod aU aV aC aT] ++
  storeA aX₂ sQi sPl sMask ++ storeA aX₁ sDp sPl sMask ++ storeA aV sDq sQl sMask ++
  [.block retMask])

/-- `vg_rsa_crt_values`. -/
def code : Prog isa :=
  .seq (.block (entry ++ invalid)) (.ite (.zero .x .x9) fail main)

end CrtValues

end VG.Impl.Rsa.AArch64.Keys
