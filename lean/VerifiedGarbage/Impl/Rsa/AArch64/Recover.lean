import VerifiedGarbage.Impl.Rsa.AArch64.Keys

/-!
# `vg_rsa_recover_primes` on AArch64

`vg_rsa_recover_primes(p, p_len, q, q_len, n, n_len, e, e_len, d, d_len,
scratch, scratch_len)`: the first eight arguments in `x0`–`x7`, the others
on the stack, in the layout of `Keys.lean` with 16 arrays. `n` is checked
as `vg_rsa_public` checks it (it is public). Then x86-64's computation
(`Impl/Rsa/X86_64/Recover.lean`), with Montgomery multiplication `mul`
(`[o] = [a] [b] R⁻¹ mod n`):

* `M = d e` over two arrays (`prod`), by `mulRows`, a row per word of `e`;
  if `M` is even or 1 (`d e - 1` odd or not positive), no candidate is
  tried and zeros are written. Otherwise `m = M - 1` (`M` with its low bit
  cleared), and `64 Bw` masked halvings (`Bw` the words of `d` and `e`
  together, public) leave `r = m / 2^t` with `r` odd and `t` counted
  (`halving`).
* `-n⁻¹`, `R² mod n`, `R mod n` and `n - R mod n` (the Montgomery forms of
  1 and `-1`).
* For the candidates `g = 2, 3, …`, until one gives the factors or 100 are
  tried (`candLoop`, whose number of iterations is the number of tries,
  which the contract lets leak): `y = g^r` by a square and a multiplication
  per bit of `r` (all `64 Bw` of them), the multiplicand `g` or 1 chosen by
  a mask (`expLoop`); then `64 Bw` squarings under masks that stop at
  `y² = 1` (found), at `y² = -1` or after `t` of them (not found)
  (`sqBody`).
* `p = gcd(y - 1, n)` by `inverse`, `q = n / p` by `divmod`, the larger
  first, written masked by whether a candidate gave them (`fin`).

Every loop counts down a register with `cbnz`, or tests a value computed
into a register, and every comparison's carry is made a register's value by
`csel`: the model branches only on whether a register is zero.
-/

namespace VG.Impl.Rsa.AArch64.Recover

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Bignum.Public (sN sK sE sElen sMask sCnt aN aX aR2 aXm aY aOne)

/-! ## The layout -/

/-- Header slots, beside `vg_rsa_public`'s `sN`, `sK`, `sE`, `sElen`,
`sMask` and `sCnt` and the layout's `sStride`: `p` and `q`'s pointers,
`d`'s pointer and length, the candidate's number, `t`, and three slots for
the loops' counters and masks. -/
def sP : Nat := sFn 0
def sQ : Nat := sFn 5
def sD : Nat := sFn 7
def sDl : Nat := sFn 8
def sCand : Nat := sFn 9
def sT : Nat := sFn 11
def sC1 : Nat := sFn 13
def sC2 : Nat := sFn 14
def sC3 : Nat := sFn 15

/-- Arrays, after `vg_rsa_public`'s 0 to 7: `e` (8), `d` (9), `M` over 10
and 11, `g R mod n` (12), `R mod n` (13), `n - R mod n` (14), and the
halvings' temporary over 14 and 15. At the end: `gcd`'s `u`, `v`, `x₁`,
`x₂` and working array (8, 9, 12, 13, 15), and `n / p` (14) and
`n mod p` (10). -/
def aE : Nat := 8
def aD : Nat := 9
def aM : Nat := 10
def aG : Nat := 12
def aO : Nat := 13
def aNg : Nat := 14
def aH : Nat := 14
def fU : Nat := 8
def fV : Nat := 9
def fX₁ : Nat := 12
def fX₂ : Nat := 13
def fT : Nat := 15
def fQ : Nat := 14
def fR : Nat := 10

/-- `Bw = w + ⌈e_len / 8⌉` into `x14` (`w` in `x12`). -/
def bw : List Instr := [ldh .x3 sElen, .addImm .x .x3 .x3 7, .lsr .x .x3 .x3 3, .add .x .x14 .x3 .x12]

/-! ## The entry and the exits -/

/-- The arguments in the header at `scratch` (the third stack argument),
whose base goes in `x0`; then `n` and `n_len` into `x2` and `x3` for
`invalid`. `p_len` and `q_len` are `n_len`. -/
def entry : List Instr :=
  [.ldrSp .x8 16, .str .x .x0 .x8 (8 * sP), .str .x .x2 .x8 (8 * sQ), .str .x .x4 .x8 (8 * sN),
    .str .x .x5 .x8 (8 * sK), .str .x .x6 .x8 (8 * sE), .str .x .x7 .x8 (8 * sElen),
    .ldrSp .x9 0, .str .x .x9 .x8 (8 * sD), .ldrSp .x9 8, .str .x .x9 .x8 (8 * sDl), mov .x0 .x8,
    mov .x2 .x4, mov .x3 .x5]

/-- Zeros to `p` and `q`, and 0 returned. -/
def fail : Prog isa := seqs [zeroOut sP sK, zeroOut sQ sK, .block [movi .x0 0]]

/-! ## `d e` -/

/-- `-n⁻¹`, for `n` in its array. -/
def minvBlk : List Instr := ws ++ base aN .x16 ++ [ld .x3 .x16] ++ minv ++ [sth .x15 sMinv]

/-- `M := d e`: `M += e_j d` at word `j`, for each word `j` of `e`. -/
def prod : List (Prog isa) :=
  [zeroA aM, zeroA (aM + 1),
    .block (ws ++ base aE .x5 ++ base aD .x9 ++ base aM .x8 ++
      [mov .x11 .x5, ldh .x3 sElen, .addImm .x .x3 .x3 7, .lsr .x .x13 .x3 3, movi .x7 0]),
    Crt.mulRows]

/-- The mask of `M` even into `sC2`, and `m := M` with its low bit cleared
(`M - 1` for an odd `M`); `x14 := Bw` and `x9 := 0` for the test of
`m = 0`, and `x16` at `m`. -/
def skipBlk : List Instr :=
  ws ++ base aM .x16 ++
    [ld .x3 .x16, movi .x4 1, .logic .and .x .x5 .x3 .x4, .sub .x .x3 .x3 .x5, st .x3 .x16,
      .subImm .x .x5 .x5 1, sth .x5 sC2, movi .x9 0] ++ bw

/-- `x9 |= [x16]`, a word at a time. -/
def orLoop : Prog isa := countLoop .x14 [ld .x3 .x16, .logic .orr .x .x9 .x9 .x3, next .x16]

/-- `x10 = 0` iff `M` is odd and `m ≠ 0`: the mask of `m = 0` (`x9 - 1`
borrows) or'ed with `sC2`. -/
def skipTest : List Instr :=
  [movi .x7 0, movi .x4 1, .subs .x .x3 .x9 .x4] ++ borrowMask ++ [ldh .x3 sC2, .logic .orr .x .x10 .x15 .x3]

/-! ## `m = 2^t r` -/

/-- `x6 := 64 Bw` halvings, and `t := 0`. -/
def halfInit : List Instr := ws ++ bw ++ [.lsl .x .x6 .x14 6, movi .x3 0, sth .x3 sT]

/-- `[aH] := m / 2` over `Bw` words; `x15` the mask of `m` even; `t += 1`
if it is; and the bases for `m := [aH]` under the mask. -/
def halfShift : List (Prog isa) := [
  .block (ws ++ bw ++ base aM .x16 ++ base aH .x17),
  countLoop .x14 shrBody,
  .block (ws ++ bw ++ base aH .x16 ++ base aM .x17 ++
    [ld .x3 .x17, movi .x4 1, .logic .and .x .x3 .x3 .x4, .subImm .x .x15 .x3 1, ldh .x3 sT, .sub .x .x3 .x3 .x15,
      sth .x3 sT])]

/-- `64 Bw` times: `m := m / 2` if `m` is even, and then `t += 1`. -/
def halving : Prog isa :=
  .seq (.block halfInit) (.loop (seqs (halfShift ++ [Crt.selLoop, .block [.subImm .x .x6 .x6 1]])) (.nonzero .x .x6))

/-! ## The candidates -/

variable (mul : Nat → Nat → Nat → Prog isa)

/-- `R² mod n` as `vg_rsa_public_precompute` computes it, the number 1,
`R mod n` and `n - R mod n`. -/
def mont : List (Prog isa) :=
  r2Steps mul ++
  [.block [ldh .x12 sW, movi .x9 1, movi .x13 0], setWord aOne,
    mul aY aR2 aOne,
    copyA aO aY,
    .block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base aN .x16 ++ base aO .x17 ++
      base aNg .x13),
    countLoop .x14 subBody]

/-- The candidate `g = sCand + 2` into `x9`, `x13 := 0`, and `w`. -/
def gBlk : List Instr := [ldh .x9 sCand, .addImm .x .x9 .x9 2, movi .x13 0, ldh .x12 sW]

/-- `sC1 := Bw`, the words of `r` left. -/
def expInit : List Instr := ws ++ bw ++ [sth .x14 sC1]

/-- Word `sC1 - 1` of `r` into `sC2`, and `sC3 := 64` bits left. -/
def wordHead : List Instr :=
  ws ++ base aM .x16 ++
    [ldh .x3 sC1, .subImm .x .x3 .x3 1, .lsl .x .x3 .x3 3, .add .x .x16 .x16 .x3, ld .x3 .x16, sth .x3 sC2,
      movi .x3 64, sth .x3 sC3]

/-- The top bit of `sC2` out of it, and `x15` the mask of it set; the
bases of `g R mod n` and of the multiplicand. -/
def bitSel : List Instr :=
  [ldh .x3 sC2, .lsr .x .x4 .x3 63, .add .x .x3 .x3 .x3, sth .x3 sC2, movi .x7 0, .sub .x .x15 .x7 .x4] ++ ws ++
    base aG .x16 ++ base aXm .x17 ++ [mov .x14 .x12]

/-- The bits left, into `x3`. -/
def bitNext : List Instr := [ldh .x3 sC3, .subImm .x .x3 .x3 1, sth .x3 sC3]

/-- A bit of `r`: the multiplicand `g` or 1 (in Montgomery form), then
`Y := Y² · multiplicand`. -/
def bitBody : Prog isa :=
  seqs [copyA aXm aO, .block bitSel, Crt.selLoop, mul aY aY aY, mul aY aY aXm, .block bitNext]

/-- The words left, into `x3`. -/
def wordNext : List Instr := [ldh .x3 sC1, .subImm .x .x3 .x3 1, sth .x3 sC1]

/-- `Y := Y · g^r` (in Montgomery form), over all the bits of the `Bw` words
of `r`, most significant first. -/
def expLoop : Prog isa :=
  .seq (.block expInit)
    (.loop (.seq (.block wordHead) (.seq (.loop (bitBody mul) (.nonzero .x .x3)) (.block wordNext)))
      (.nonzero .x .x3))

/-- `x15 :=` the mask of `x9 = 0` (`x9 - 1` borrows). -/
def zeroMask : List Instr := [movi .x7 0, movi .x4 1, .subs .x .x3 .x9 .x4] ++ borrowMask

/-- `done := (y = 1) ∨ (y = -1)` (`y = 1` in `sC2`), `ok := 0`, `k := 0`. -/
def chkBlk : List Instr :=
  zeroMask ++ [ldh .x3 sC2, .logic .orr .x .x15 .x15 .x3, sth .x15 sC2, sth .x7 sC3, sth .x7 sC1]

/-- After `x = y²`, with `x = 1` in `sMask` and `x9 = 0` iff `x = -1`: the
squaring is live if not `done` and `k < t`; it finds `y` if `x = 1`, fails
if `x = -1` or `k + 1 = t`, and continues with `y := x` otherwise.
`done` and `ok` updated, and `x15` the mask of continuing. -/
def sqMasks : List Instr :=
  zeroMask ++ [mov .x10 .x15,
    ldh .x3 sC1, ldh .x4 sT, .subs .x .x3 .x3 .x4] ++ borrowMask ++ [mov .x5 .x15,
    ldh .x3 sC1, .addImm .x .x3 .x3 1, ldh .x4 sT, .logic .eor .x .x3 .x3 .x4, movi .x4 1, .subs .x .x3 .x3 .x4] ++
    borrowMask ++
  [.logic .orr .x .x10 .x10 .x15,
    .subImm .x .x4 .x7 1, ldh .x3 sC2, .logic .eor .x .x3 .x3 .x4, .logic .and .x .x5 .x5 .x3,
    ldh .x2 sMask, .logic .and .x .x13 .x5 .x2,
    .logic .orr .x .x3 .x2 .x10, .logic .and .x .x3 .x3 .x5, ldh .x1 sC2, .logic .orr .x .x3 .x3 .x1, sth .x3 sC2,
    ldh .x3 sC3, .logic .orr .x .x3 .x3 .x13, sth .x3 sC3,
    .logic .orr .x .x3 .x2 .x10, .logic .eor .x .x3 .x3 .x4, .logic .and .x .x15 .x5 .x3]

/-- `sqMasks`, then the bases of `x` and `y`. -/
def sqLogic : List Instr := sqMasks ++ (ws ++ base aX .x16 ++ base aY .x17 ++ [mov .x14 .x12])

/-- `k += 1`, and `64 Bw - k` into `x3`. -/
def sqNext : List Instr :=
  ws ++ bw ++ [.lsl .x .x4 .x14 6, ldh .x3 sC1, .addImm .x .x3 .x3 1, sth .x3 sC1, .sub .x .x3 .x4 .x3]

/-- A squaring: `x := y²`, the masks of `x = ±1`, and `y := x` if the
squarings continue. -/
def sqBody : Prog isa :=
  seqs ([copyA aX aY, mul aX aX aY] ++ eqA aX aO ++ [.block (zeroMask ++ [sth .x15 sMask])] ++ eqA aX aNg ++
    [.block sqLogic, Crt.selLoop, .block sqNext])

/-- The candidates tried `+= 1`, and `x15` nonzero to go on: fewer than 100
tried and not `ok`. -/
def candNext : List Instr :=
  [ldh .x3 sCand, .addImm .x .x3 .x3 1, sth .x3 sCand, movi .x4 100, movi .x7 0, .subs .x .x3 .x3 .x4] ++
    borrowMask ++ [ldh .x3 sC3, .logic .eor .x .x3 .x3 .x4, .logic .and .x .x15 .x15 .x3]

/-- A candidate: `g R mod n`, `Y = g^r R mod n`, the check of `y = ±1`,
and the squarings. -/
def candBody : Prog isa :=
  seqs ([.block gBlk, setWord aX, mul aXm aX aR2, copyA aG aXm, copyA aY aO, expLoop mul] ++ eqA aY aO ++
    [.block (zeroMask ++ [sth .x15 sC2])] ++ eqA aY aNg ++
    [.block chkBlk, .loop (sqBody mul) (.nonzero .x .x3), .block candNext])

/-- The candidates, from `sCand = 0`. -/
def candLoop : Prog isa :=
  .seq (.block [movi .x3 0, sth .x3 sCand]) (.loop (candBody mul) (.nonzero .x .x15))

/-- The mask of the last candidate's `ok`; `y` out of Montgomery form,
`p = gcd(y - 1, n)` and `q = n / p`, the larger first; both written
masked, and the mask's low bit returned. -/
def fin : List (Prog isa) :=
  [.block [ldh .x3 sC3, sth .x3 sMask],
    mul aY aY aOne, zeroA fU,
    .block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base aY .x16 ++ base aOne .x17 ++
      base fU .x13),
    countLoop .x14 subBody,
    zeroA fV, copyA fV aN, zeroA fX₁, .block (setOneA fX₁), zeroA fX₂, inverse fU fV fX₁ fX₂ aN fT,
    zeroA fQ, copyA fQ aN, divmod fQ fR fV fT,
    .block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base fV .x16 ++ base fQ .x17),
    cmpLoop,
    .block (borrowMask ++ [mov .x14 .x12] ++ base fV .x16 ++ base fQ .x17),
    countLoop .x14 cswapBody] ++
  storeA fV sP sK sMask ++ storeA fQ sQ sK sMask ++ [.block retMask]

/-- After `M` is known odd and above 1. -/
def rest : Prog isa := seqs ([halving] ++ mont mul ++ [candLoop mul] ++ fin mul)

/-- The computation, once `n` is known valid. -/
def main : Prog isa := seqs ([.block Keys.head] ++ loadA aN sN sK ++ loadA aE sE sElen ++ loadA aD sD sDl ++
  [.block minvBlk] ++ prod ++
  [.block skipBlk, orLoop, .block skipTest, .ite (.zero .x .x10) (rest mul) fail])

/-- `vg_rsa_recover_primes` with Montgomery multiplication `mul`. -/
def code : Prog isa :=
  .seq (.block (entry ++ invalid)) (.ite (.zero .x .x9) fail (main mul))

end VG.Impl.Rsa.AArch64.Recover
