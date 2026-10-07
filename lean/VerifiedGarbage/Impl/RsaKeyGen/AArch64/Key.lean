import VerifiedGarbage.Impl.Rsa.AArch64.Keys
import VerifiedGarbage.Impl.RsaKeyGen.AArch64.Candidate

/-!
# An RSA key from its two primes on AArch64

`vg_rsa_keygen_key(n, n_len, d, d_len, p, p_len, q, q_len, dp, dp_len, dq,
dq_len, qinv, qinv_len, e, e_len, scratch, scratch_len)`: the first eight
arguments in `x0`–`x7`, the others on the stack (`[sp]` to `[sp + 72]`).

x86-64's computation (`Impl/RsaKeyGen/X86_64/Key.lean`), piece by piece, in
the layout of the RSA key routines (`Impl/Rsa/AArch64/Keys.lean`): a header
of 32 words and arrays of `W + 2` words after it, for the `W = n_len / 8`
words of `n` (the primes have `w = W / 2`), array `j` at `256 + 8 (W + 2) j`,
its base computed from `x0` and the stride. The routines of `Keys`
(`divmod`, `inverse`, `loadA`, `storeA`, …) do the arithmetic; the products
are `Crt.mulRows` and `mulAddRow`. The public exponent `e` (`e_len ≤ 8`
octets) is a word, public: the code branches on it. Its timing depends on
nothing else but the lengths and the status returned.

1. `p` and `q` are loaded, and swapped (under the mask of `p < q`) so that
   `p ≥ q`.
2. `p − 1` and `q − 1` (0 for 0): the number minus the constant 1 and'ed
   with the mask of its being nonzero.
3. `lcm(p − 1, q − 1)`: their product `φ` (`w` words each); then `64 W`
   steps that halve `u`, `v` (copies of `p − 1` and `q − 1`) and `φ` while
   `u` and `v` are both even; `v` made odd by a swap (if it is even);
   `gcd(u, v)` by `inverse` (modulo `v`, 3 for `v < 2`); and `φ` divided by
   it (1 for `v < 2`).
4. `d = e⁻¹ mod L`, and the mask `kOk` of its existence:
   * `e = 0`: none.
   * `e = 1`: `d = 1`, for `L ≠ 1`.
   * `e` odd: `L = e Q + R` by `divmod`; `x = R⁻¹ mod e` by `inverse`, for
     `gcd(R, e) = 1` and `L ≥ 2`; then with `t = e − x`,
     `d = Q t + (1 + R t) / e`, the last a word: `(1 + R t) e⁻¹ mod 2⁶⁴`
     (`minv`'s inverse of `e`, left in `x4`).
   * `e` even: `d = (e mod L)⁻¹ mod L` by `inverse`, for an odd `L ≥ 3`
     (the modulus 3 otherwise).
5. If `kOk` and `d ≤ 2^(64 w)`: zeros to all seven outputs, and 2.
6. Otherwise `qInv` by `inverse` (modulo `p`, or 3 for a `p` even or below
   3), `dP = d mod (p − 1)` and `dQ = d mod (q − 1)` by `divmod`, and
   `n = p q`; the mask of `kOk`, `gcd(q, p) = 1`, `n`'s top bit, `p` and `q`
   odd and `e` valid (`Rsa.exponentValid`); the seven outputs stored under
   it, and its low bit returned.

Differences from x86-64, besides the registers:

* A mask is in `x15` (x86-64's `rbp` or `r15`), as `Keys`' are, made by
  `borrowMask` or `carryMask` from a comparison's carry; so a comparison
  gives the mask of `<` (`ltA`) or of `≥` (`geA`) directly, and `eqA`'s `x9`
  gives the mask of `=` (`eqMask`) or of `≠` (`neMask`).
* `selC j` is `[j] := x15 ? [aC] : [j]` (`Crt.selLoop`), so the callers
  give it the mask of the bad case (x86-64's complement): `v < 2`, or `L`
  (or `p`) even or below 3.
* `halfIf` keeps its mask in `x15` (no header slot), and `dOdd` keeps
  `t = e − x` in `x1` and the low word `(1 + R t) e⁻¹` in `x10` (no `sMo`).
* `dEven` makes its divisor with `divisorOf aL` (x86-64's same code, without
  the unused constant 1).
* `n_len` is in `vg_rsa_public`'s `sK`, from which `Keys.head` computes `W`
  (and also sets the unused `sMask`).
* The step counter of the halving is `x6`, counted down to 0, as `divmod`'s
  and `inverse`'s.

Every branch is a `cbz`/`cbnz` on a register: on `e` (`dPart`) and on the
mask of `d` too small (the status 2). No callee-saved register is written,
and nothing is pushed.
-/

namespace VG.Impl.RsaKeyGen.AArch64.Key

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Impl.Rsa.AArch64
open VG.Impl.Rsa.AArch64.Keys
open VG.Impl.RsaKeyGen.AArch64.Candidate (loadE kE kElen)

/-! ## Header slots

`kE` and `kElen` are the candidate's (for `loadE`), `kNl` is
`vg_rsa_public`'s `sK` (for `Keys.head`), `sStride` the key routines'. -/

def kNo : Nat := sFn 0
def kDo : Nat := sFn 1
def kNl : Nat := sK
def kPp : Nat := sFn 5
def kPl : Nat := sFn 7
def kQp : Nat := sFn 8
def kDp : Nat := sFn 9
def kDq : Nat := sFn 10
def kQi : Nat := sFn 11
/-- `e`'s value. -/
def kEv : Nat := sFn 14
/-- The mask `dOk`, then the final mask. -/
def kOk : Nat := sFn 15

/-! ## Arrays -/

def aPa : Nat := 0
def aQa : Nat := 1
def aU : Nat := 2
def aV : Nat := 3
def aPm : Nat := 4
def aQm : Nat := 5
def aX₁ : Nat := 6
def aX₂ : Nat := 7
def aT : Nat := 8
def aM : Nat := 9
def aL : Nat := 10
def aQt : Nat := 11
def aR : Nat := 12
def aDd : Nat := 13
def aC : Nat := 14
def aE : Nat := 15

/-! ## Entry and exit -/

/-- The arguments in the header at `scratch` (the ninth stack argument),
whose base goes in `x0`. `d_len` is `n_len`; `q_len`, `dp_len`, `dq_len` and
`qinv_len` are `p_len`. -/
def entry : List Instr :=
  [.ldrSp .x8 64, .str .x .x0 .x8 (8 * kNo), .str .x .x1 .x8 (8 * kNl), .str .x .x2 .x8 (8 * kDo),
    .str .x .x4 .x8 (8 * kPp), .str .x .x5 .x8 (8 * kPl), .str .x .x6 .x8 (8 * kQp),
    .ldrSp .x9 0, .str .x .x9 .x8 (8 * kDp), .ldrSp .x9 16, .str .x .x9 .x8 (8 * kDq),
    .ldrSp .x9 32, .str .x .x9 .x8 (8 * kQi), .ldrSp .x9 48, .str .x .x9 .x8 (8 * kE),
    .ldrSp .x9 56, .str .x .x9 .x8 (8 * kElen), mov .x0 .x8]

/-- Zeros to the seven outputs, and the status `st` returned. -/
def zeros (st : Nat) : Prog isa := seqs [zeroOut kNo kNl, zeroOut kDo kNl, zeroOut kPp kPl, zeroOut kQp kPl,
  zeroOut kDp kPl, zeroOut kDq kPl, zeroOut kQi kPl, .block [movi .x0 st]]

/-! ## Masks -/

/-- The carry flag clear iff `[a] < [b]` over `W` words. -/
def cmpA (a b : Nat) : List (Prog isa) :=
  [.block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base a .x16 ++ base b .x17), cmpLoop]

/-- `x15 := ` the mask of `[a] < [b]` over `W` words. -/
def ltA (a b : Nat) : List (Prog isa) := cmpA a b ++ [.block borrowMask]

/-- `x15 := ` the mask of `[a] ≥ [b]` over `W` words. -/
def geA (a b : Nat) : List (Prog isa) := cmpA a b ++ [.block carryMask]

/-- `x15 := ` the mask of `x9 = 0` (`x9 − 1` borrows). -/
def zeroMask : List Instr := [movi .x7 0, movi .x4 1, .subs .x .x3 .x9 .x4] ++ borrowMask

/-- `x15 := ` the mask of `x9 ≠ 0` (`x9 − 1` does not borrow). -/
def nonzeroMask : List Instr := [movi .x7 0, movi .x4 1, .subs .x .x3 .x9 .x4] ++ carryMask

/-- `x15 := ` the mask of `[a] = [b]` over `W` words. -/
def eqMask (a b : Nat) : List (Prog isa) := eqA a b ++ [.block zeroMask]

/-- `x15 := ` the mask of `[a] ≠ [b]` over `W` words. -/
def neMask (a b : Nat) : List (Prog isa) := eqA a b ++ [.block nonzeroMask]

/-- `x15 := ~x15`. -/
def notMask : List Instr := [movi .x7 0, .subImm .x .x4 .x7 1, .logic .eor .x .x15 .x15 .x4]

/-- `[aC] := x`, a word, over `W + 2` words. -/
def constA (x : Nat) : List (Prog isa) :=
  [zeroA aC, .block (ws ++ base aC .x16 ++ [movi .x3 x, st .x3 .x16])]

/-- `[j] := x15 ? [aC] : [j]` over `W` words. -/
def selC (j : Nat) : List (Prog isa) :=
  [.block (ws ++ [mov .x14 .x12] ++ base aC .x16 ++ base j .x17), Crt.selLoop]

/-- `x15 := ` the mask of `[j]` odd. -/
def oddMaskOf (j : Nat) : List Instr := ws ++ base j .x16 ++ [movi .x7 0, ld .x3 .x16] ++ oddMask

/-- `x15 := ` the mask of `[j]` even (its low bit minus one). -/
def evenMaskOf (j : Nat) : List Instr :=
  ws ++ base j .x16 ++ [ld .x3 .x16, movi .x4 1, .logic .and .x .x3 .x3 .x4, .subImm .x .x15 .x3 1]

/-! ## The primes -/

/-- `p` and `q` swapped under the mask of `p < q`. -/
def order : List (Prog isa) :=
  ltA aPa aQa ++ [.block (ws ++ [mov .x14 .x12] ++ base aPa .x16 ++ base aQa .x17), countLoop .x14 cswapBody]

/-- `[o] := [j] - 1`, or 0 for `[j] = 0`: `[j]` minus `[aC] = 1` and'ed
with the mask of `[j] ≠ 0`. -/
def decTo (o j : Nat) : List (Prog isa) :=
  [zeroA o, copyA o j] ++ constA 0 ++ neMask j aC ++ constA 1 ++
    [.block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base o .x16 ++ base aC .x17 ++ base o .x8),
      countLoop .x14 subMBody]

/-! ## `lcm(p − 1, q − 1)` -/

/-- `[o] := [a] [b]`, `w = W / 2` words each (`x11` set last, as `base`
uses it). -/
def mulTo (o a b : Nat) : List (Prog isa) :=
  [zeroA o, .block (ws ++ base b .x9 ++ base o .x8 ++ base a .x16 ++
    [mov .x11 .x16, .lsr .x .x12 .x12 1, mov .x13 .x12, movi .x7 0]), Crt.mulRows]

/-- `[aL] := [aPm] [aQm]`. -/
def phi : List (Prog isa) := mulTo aL aPm aQm

/-- `[j] := x15 ? [j] / 2 : [j]` (`[aT]` working space). -/
def halfIf (j : Nat) : List (Prog isa) :=
  [.block (ws ++ [mov .x14 .x12] ++ base j .x16 ++ base aT .x17), countLoop .x14 shrBody,
    .block (ws ++ [mov .x14 .x12] ++ base aT .x16 ++ base j .x17), Crt.selLoop]

/-- One step of the halving: the mask of `u` and `v` both even into `x15`,
then `u`, `v` and `φ` halved under it, and the step counter `x6` counted
down. -/
def twoStep : Prog isa := seqs ([
  .block (ws ++ base aU .x16 ++ base aV .x17 ++ [ld .x3 .x16, ld .x4 .x17, .logic .orr .x .x3 .x3 .x4, movi .x4 1,
    .logic .and .x .x3 .x3 .x4, .subImm .x .x15 .x3 1])] ++
  halfIf aU ++ halfIf aV ++ halfIf aL ++ [.block [.subImm .x .x6 .x6 1]])

/-- `64 W` steps of the halving. -/
def twos : List (Prog isa) := [.block (ws ++ [.lsl .x .x6 .x12 6]), .loop twoStep (.nonzero .x .x6)]

/-- `[aV] := gcd(u, v)`, or 1 for `v < 2`, after the halving: `v` made odd
by a swap, `inverse` modulo `v` (3 for `v < 2`), and the result 1 for
`v < 2` (whose mask `kOk` holds). -/
def gcdUV : List (Prog isa) :=
  [.block (evenMaskOf aV ++ [mov .x14 .x12] ++ base aU .x16 ++ base aV .x17), countLoop .x14 cswapBody] ++
  constA 2 ++ ltA aV aC ++ [.block [sth .x15 kOk]] ++ constA 3 ++ [.block [ldh .x15 kOk]] ++ selC aV ++
  [zeroA aM, copyA aM aV, zeroA aX₁, .block (setOneA aX₁), zeroA aX₂, inverse aU aV aX₁ aX₂ aM aT] ++
  constA 1 ++ [.block [ldh .x15 kOk]] ++ selC aV

/-- `[aL] := lcm(p − 1, q − 1)`. -/
def lcmPart : List (Prog isa) :=
  phi ++ [zeroA aU, copyA aU aPm, zeroA aV, copyA aV aQm] ++ twos ++ gcdUV ++ [divmod aL aR aV aT]

/-! ## `d = e⁻¹ mod L` -/

/-- `[aE] := e`. -/
def loadEv : List (Prog isa) :=
  [zeroA aE, .block (ws ++ base aE .x16 ++ [ldh .x3 kEv, st .x3 .x16])]

/-- `kOk := ` the mask of `L ≥ 2`. -/
def lGe2 : List (Prog isa) := constA 2 ++ geA aL aC ++ [.block [sth .x15 kOk]]

/-- `e = 0`: no inverse. -/
def dZero : List Instr := [movi .x3 0, sth .x3 kOk]

/-- `e = 1`: `d = 1`, for `L ≠ 1`. -/
def dOne : List (Prog isa) :=
  constA 1 ++ neMask aL aC ++ [.block [sth .x15 kOk], zeroA aDd, .block (setOneA aDd)]

/-- `inverse`'s start for `[aU]` modulo `[j]`: `v := [j]`, `x₁ := 1`,
`x₂ := 0`. -/
def invFrom (j : Nat) : List (Prog isa) :=
  [zeroA aV, copyA aV j, zeroA aX₁, .block (setOneA aX₁), zeroA aX₂]

/-- `kOk &= ` the mask of `[aV] = 1`. -/
def gcdIsOne : List (Prog isa) :=
  constA 1 ++ eqMask aV aC ++ [.block [ldh .x3 kOk, .logic .and .x .x15 .x15 .x3, sth .x15 kOk]]

/-- `e` odd, at least 3: `L = e Q + R`, `x = R⁻¹ mod e`, `t = e − x` (in
`x1`), then `d = Q t + c` with `c = (1 + R t) e⁻¹ mod 2⁶⁴` (in `x10`; `e⁻¹`
is `minv`'s `x4`). -/
def dOdd : List (Prog isa) :=
  loadEv ++ [zeroA aQt, copyA aQt aL, divmod aQt aR aE aT, zeroA aU, copyA aU aR] ++ invFrom aE ++
  [inverse aU aV aX₁ aX₂ aE aT] ++ lGe2 ++ gcdIsOne ++
  [.block ([ldh .x3 kEv] ++ minv ++ ws ++ base aX₂ .x16 ++ base aR .x17 ++
      [ldh .x1 kEv, ld .x3 .x16, .sub .x .x1 .x1 .x3, ld .x3 .x17, .mul .x .x3 .x3 .x1, .addImm .x .x3 .x3 1,
        .mul .x .x10 .x3 .x4]),
    zeroA aDd,
    .block (ws ++ base aDd .x8 ++ [st .x10 .x8] ++ base aQt .x9 ++ [movi .x7 0]),
    mulAddRow]

/-- `[aM] := [j]`, or 1 for `[j] = 0`. -/
def divisorOf (j : Nat) : List (Prog isa) :=
  [zeroA aM, copyA aM j] ++ constA 0 ++ eqMask j aC ++
  [.block (ws ++ base aM .x16 ++ [ld .x3 .x16, movi .x4 1, .logic .and .x .x4 .x15 .x4, .logic .orr .x .x3 .x3 .x4,
      st .x3 .x16])]

/-- `e` even: `d = (e mod L)⁻¹ mod L` for an odd `L ≥ 3`. -/
def dEven : List (Prog isa) :=
  loadEv ++ divisorOf aL ++ [zeroA aQt, copyA aQt aE, divmod aQt aR aM aT, zeroA aU, copyA aU aR] ++
  -- `x15 := ` the mask of `L` even or below 3, `kOk` its complement; `[aM] := L`, or 3.
  constA 3 ++ ltA aL aC ++
  [.block ([mov .x10 .x15] ++ evenMaskOf aL ++ [.logic .orr .x .x15 .x15 .x10, mov .x10 .x15] ++ notMask ++
      [sth .x15 kOk, mov .x15 .x10]),
    zeroA aM, copyA aM aL] ++ selC aM ++ invFrom aM ++ [inverse aU aV aX₁ aX₂ aM aT] ++ gcdIsOne ++
  [zeroA aDd, copyA aDd aX₂]

/-- `d` and `kOk`, by `e`. -/
def dPart : Prog isa :=
  .seq (.block [ldh .x3 kEv])
    (.ite (.zero .x .x3) (.block dZero)
      (.seq (.block [.subImm .x .x3 .x3 1])
        (.ite (.zero .x .x3) (seqs dOne)
          (.seq (.block [ldh .x3 kEv, movi .x4 1, .logic .and .x .x3 .x3 .x4])
            (.ite (.nonzero .x .x3) (seqs dOdd) (seqs dEven))))))

/-! ## The key -/

/-- `x15 := kOk & ` the mask of `d ≤ 2^(64 w)` (`d < 2^(64 w) + 1`, word
`w = W / 2` of `[aC]` set). -/
def smallMask : List (Prog isa) :=
  constA 1 ++
  [.block (ws ++ base aC .x16 ++ [.lsr .x .x3 .x12 1, .lsl .x .x3 .x3 3, .add .x .x16 .x16 .x3, movi .x3 1,
      st .x3 .x16])] ++
  ltA aDd aC ++ [.block [ldh .x3 kOk, .logic .and .x .x15 .x15 .x3]]

/-- `qInv` into `aX₂` (modulo `p`, or 3 for a `p` even or below 3) and
`kOk &= ` the mask of `gcd(q, p) = 1`. -/
def qinvPart : List (Prog isa) :=
  [zeroA aU, copyA aU aQa] ++ constA 3 ++ ltA aPa aC ++
  [.block ([mov .x10 .x15] ++ evenMaskOf aPa ++ [.logic .orr .x .x15 .x15 .x10]), zeroA aM, copyA aM aPa] ++
  selC aM ++ invFrom aM ++ [inverse aU aV aX₁ aX₂ aM aT] ++ gcdIsOne

/-- `dP` into `aX₁` and `dQ` into `aV`. -/
def crtPart : List (Prog isa) :=
  divisorOf aPm ++ [zeroA aU, copyA aU aDd, divmod aU aV aM aT, zeroA aX₁, copyA aX₁ aV] ++
  divisorOf aQm ++ [zeroA aU, copyA aU aDd, divmod aU aV aM aT]

/-- `n = p q` into `aQt`. -/
def nPart : List (Prog isa) := mulTo aQt aPa aQa

/-- `kOk &= ` the masks of `n`'s top bit, `p` and `q` odd, and `e` valid
(`Rsa.exponentValid`: odd, at least 3 and below `2^33`), and'ed in `x10`. -/
def finalMask : List Instr :=
  ws ++ base aQt .x16 ++
  [.lsl .x .x3 .x12 3, .add .x .x16 .x16 .x3, .subImm .x .x16 .x16 8, ld .x3 .x16, .lsr .x .x3 .x3 63, movi .x7 0,
    .sub .x .x10 .x7 .x3, ldh .x3 kOk, .logic .and .x .x10 .x10 .x3] ++
  oddMaskOf aPa ++ [.logic .and .x .x10 .x10 .x15] ++ oddMaskOf aQa ++ [.logic .and .x .x10 .x10 .x15] ++
  -- `e`: odd, `e − 3` without a borrow, `(e >> 33) − 1` with one.
  [ldh .x3 kEv] ++ oddMask ++ [.logic .and .x .x10 .x10 .x15] ++
  [ldh .x3 kEv, movi .x4 3, .subs .x .x3 .x3 .x4] ++ carryMask ++ [.logic .and .x .x10 .x10 .x15] ++
  [ldh .x3 kEv, .lsr .x .x3 .x3 33, movi .x4 1, .subs .x .x3 .x3 .x4] ++ borrowMask ++
  [.logic .and .x .x10 .x10 .x15, sth .x10 kOk]

/-- The seven outputs under `kOk`, and its low bit returned. -/
def outputs : List (Prog isa) :=
  storeA aQt kNo kNl kOk ++ storeA aDd kDo kNl kOk ++ storeA aPa kPp kPl kOk ++ storeA aQa kQp kPl kOk ++
  storeA aX₁ kDp kPl kOk ++ storeA aV kDq kPl kOk ++ storeA aX₂ kQi kPl kOk ++
  [.block [ldh .x3 kOk, movi .x4 1, .logic .and .x .x0 .x3 .x4]]

/-- Once `d` is not too small, or does not exist. -/
def keyPart : Prog isa :=
  seqs (qinvPart ++ crtPart ++ nPart ++ [.block finalMask] ++ outputs)

/-- `vg_rsa_keygen_key`. -/
def code : Prog isa :=
  seqs ([.block (entry ++ Keys.head)] ++ loadA aPa kPp kPl ++ loadA aQa kQp kPl ++ loadE ++
    [.block [sth .x3 kEv]] ++ order ++ decTo aPm aPa ++ decTo aQm aQa ++ lcmPart ++ [dPart] ++
    smallMask ++ [.ite (.nonzero .x .x15) (zeros 2) keyPart])

end VG.Impl.RsaKeyGen.AArch64.Key
