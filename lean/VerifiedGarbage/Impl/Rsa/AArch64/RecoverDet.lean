module

public import VerifiedGarbage.Impl.Rsa.AArch64.Recover

/-!
# `vg_rsa_recover_primes_det` on AArch64: SP 800-56B Rev. 2 Appendix C.2

`vg_rsa_recover_primes`' arguments, entry and exits (`Recover.lean`), and
`Keys.lean`'s layout at two widths, which the code switches between by
rewriting the header (`setNar`, `setWid`): narrow numbers of
`v = ⌈k / 8⌉ + 1` words and wide ones of `W = 2 v + 2` words, wide array `j`
being narrow arrays `2 j` and `2 j + 1`. Then, without a branch on a
secret (`Proof/Rsa/RecoverDetModel.lean`'s computation):

* `n`, `e`, `d` loaded (narrow), `M = d e` (`Recover.prod`, narrow arrays
  10 and 11: wide array 5);
* `X = M - 1` (wide), and `M ≥ 1`, `X ≥ 1` and'ed into the mask;
* `64 v` halvings (`twosBody`): `u` (from `n - 1`) halved while even, and
  while `x` (narrow, from `X`) is even too, `x` halved and `X` doubled;
* `gcd(u, x)` by `Keys.inverse` modulo the odd `u` (1 if `u = 1`), and
  `a = gcd · X` by `64 v` steps of a bit-serial product (`prodBody`);
* `m = a / n`, `r = a mod n` (wide `divmod`), `m < n` and'ed into the mask;
  `m + 1`, `n - r`, their quotient `q` and remainder (narrow `divmod`),
  the remainder zero and'ed into the mask;
* `b = q + 1`, `b²` (`prodBody`), `b² - 4 n` and its checks;
* its integer square root, two bits at a time (`sqrtBody`, `32 W` steps),
  the remainder zero and'ed into the mask;
* `p = (b + ϒ) / 2` and `q = (b - ϒ) / 2`, written under the mask.

Every loop's count is a function of the public `k`; every check is a mask.
-/

@[expose] public section

namespace VG.Impl.Rsa.AArch64.RecoverDet

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys
open VG.Impl.Bignum.Public (sN sK sE sElen sMask aN)
open VG.Impl.Rsa.AArch64.Recover (sP sQ sD sDl aE aD aM entry fail prod zeroMask)

/-! ## The widths -/

/-- `w` in `x12` into the header: its slot, the arrays' bases and the
stride. -/
def setW : List Instr :=
  [sth .x12 sW] ++ setBases ++ [.addImm .x .x3 .x12 2, .lsl .x .x3 .x3 3, sth .x3 sStride]

/-- The narrow width `v = ⌈k / 8⌉ + 1` into `x12`. -/
def narW : List Instr := [ldh .x3 sK, .addImm .x .x12 .x3 15, .lsr .x .x12 .x12 3]

/-- The header at the narrow width. -/
def setNar : List Instr := narW ++ setW

/-- The header at the wide width `2 v + 2`. -/
def setWid : List Instr := narW ++ [.add .x .x12 .x12 .x12, .addImm .x .x12 .x12 2] ++ setW

/-! ## Operations on arrays at the header's width -/

/-- `[o] := [a] - [b]`, and `x15` the mask of no borrow. -/
def subA (o a b : Nat) : Prog isa :=
  seqs [.block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base a .x16 ++ base b .x17 ++
    base o .x13), countLoop .x14 subBody, .block carryMask]

/-- `[o] := ([a] & x15) + [b]` (`o` neither `a` nor `b`). -/
def addA (o a b : Nat) : Prog isa :=
  .seq (.block (ws ++ [movi .x7 0, mov .x14 .x12, .adds .x .x3 .x7 .x7] ++ base a .x10 ++ base b .x8 ++
    base o .x5)) (countLoop .x14 addMBody)

/-- `x15` all ones. -/
def ones : List Instr := [movi .x7 0, .subImm .x .x15 .x7 1]

/-- `[o] := [a] / 2`, word `w` of `[a]` the bit shifted in. -/
def halfA (o a : Nat) : Prog isa :=
  .seq (.block (ws ++ [mov .x14 .x12] ++ base a .x16 ++ base o .x17)) (countLoop .x14 shrBody)

/-- `[o] := [a]` if `x15` is all ones. -/
def selA (o a : Nat) : Prog isa :=
  .seq (.block (ws ++ [mov .x14 .x12] ++ base a .x16 ++ base o .x17)) Crt.selLoop

/-- `[a] := 2 [a] + C` for the carry flag `C` that `cin` sets (`x7 = 0`),
and `cout` after it. -/
def dblA (a : Nat) (cin cout : List Instr) : Prog isa :=
  seqs [.block (ws ++ [movi .x7 0, mov .x14 .x12] ++ base a .x16 ++ cin), countLoop .x14 shlBody, .block cout]

/-- The carry flag clear. -/
def c0 : List Instr := [.adds .x .x3 .x7 .x7]

/-- The carry flag set. -/
def c1 : List Instr := [.subs .x .x3 .x7 .x7]

/-- The carry flag set iff `r` is not zero (it is 0 or 1). -/
def cOf (r : Reg) : List Instr := [movi .x4 1, .subs .x .x3 r .x4]

/-- The carry flag into `r` (`x7 = 0`). -/
def cTo (r : Reg) : List Instr := [.adc .x r .x7 .x7]

/-- The mask in `x15` and'ed into `sMask`. -/
def andMask : List Instr := [ldh .x3 sMask, .logic .and .x .x3 .x3 .x15, sth .x3 sMask]

/-- `[a] := 1` (all its words). -/
def oneA (a : Nat) : List (Prog isa) := [zeroA a, .block (setOneA a)]

/-! ## Arrays

Narrow: `n` (0), one (1), `e` (8) and `d` (9) at first, and working
arrays. Wide: `M = d e` (5), `X` and then `2^k X` (6), the product and the
quotient (7), one (8), temporaries (9), and `n` (4, narrow array 8). -/

def nOne : Nat := 1
def wM : Nat := 5
def wX : Nat := 6
def wA : Nat := 7
def wOne : Nat := 8
def wT : Nat := 9
def wN : Nat := 4

/-! ## `d e - 1` -/

def deMinus : Prog isa :=
  seqs ([.block setWid] ++ oneA wOne ++ [subA wX wM wOne, .block andMask, subA wT wX wOne, .block andMask])

/-! ## The halvings

`u` in narrow array 2, `x` in 3, the wide `X` in wide array 6. -/

def nU : Nat := 2
def nXn : Nat := 3
def nT : Nat := 4

/-- `x1` the mask of `u` even, `x2` that of `u` and `x` even. -/
def twosFlags : List Instr :=
  ws ++ base nU .x16 ++ [ld .x3 .x16, movi .x4 1, .logic .and .x .x3 .x3 .x4, .subImm .x .x1 .x3 1] ++
    base nXn .x16 ++ [ld .x3 .x16, .logic .and .x .x3 .x3 .x4, .subImm .x .x2 .x3 1, .logic .and .x .x2 .x2 .x1]

def twosBody : Prog isa := seqs [
  .block twosFlags,
  halfA nT nU, .block [mov .x15 .x1], selA nU nT,
  halfA nT nXn, .block [mov .x15 .x2], selA nXn nT,
  .block (setWid ++ [mov .x15 .x2]), addA wT wX wX, copyA wX wT,
  .block (setNar ++ [.subImm .x .x6 .x6 1])]

/-- `64 v` steps into `x6`. -/
def countN : List Instr := ws ++ [.lsl .x .x6 .x12 6]

def twos : Prog isa := seqs ([.block setNar] ++ oneA nOne ++
  [zeroA nU, subA nU aN nOne, zeroA nXn, copyA nXn (2 * wX), .block countN, .loop twosBody (.nonzero .x .x6)])

/-! ## The GCD -/

def gM : Nat := 4
def gX₁ : Nat := 5
def gX₂ : Nat := 6
def gT : Nat := 7

/-- `gcd(u, x)` into `u`'s array (by `inverse` modulo `u`, and 1 for
`u = 1`), and its copy into `y`. -/
def gcd : Prog isa := seqs ([zeroA gM, copyA gM nU] ++ oneA gX₁ ++ [zeroA gX₂, inverse nXn nU gX₁ gX₂ gM gT] ++
  eqA gM nOne ++ [.block zeroMask, selA nU nOne, zeroA gT, copyA gT nU])

/-! ## Products

`[a] += y x` by the `64 v` bits of the narrow `y`, `x` doubled at each, the
sum through `t` (wide). -/

def prodBody (y x a t : Nat) : Prog isa := seqs [
  .block (ws ++ base y .x16 ++ [ld .x3 .x16, movi .x7 0] ++ oddMask), halfA y y,
  .block setWid, addA t x a, copyA a t, dblA x c0 [],
  .block (setNar ++ [.subImm .x .x6 .x6 1])]

def product (y x a t : Nat) : Prog isa := .seq (.block countN) (.loop (prodBody y x a t) (.nonzero .x .x6))

/-- `a = gcd · 2^k X` into wide array 7. -/
def aProd : Prog isa := seqs [.block setWid, zeroA wA, .block setNar, product gT wX wA wT]

/-! ## The divisions -/

def nN : Nat := 2 * wN
def nM1 : Nat := 2
def nD : Nat := 3
def nRem : Nat := 4
def nDt : Nat := 5
def nZ : Nat := 5

/-- `m` and `r` (wide arrays 7 and 6), and `m < n` and'ed into the mask. -/
def divA : Prog isa := seqs [.block setWid, zeroA wN, .block setNar, copyA nN aN, .block setWid,
  divmod wA wX wN wT,
  .block (ws ++ [movi .x7 0, mov .x14 .x12, .subs .x .x3 .x7 .x7] ++ base wA .x16 ++ base wN .x17), cmpLoop,
  .block (borrowMask ++ andMask)]

/-- `m + 1` and `n - r`, their quotient into 3 and remainder into 4, and the
remainder zero and'ed into the mask. -/
def divB : Prog isa := seqs ([.block (setNar ++ ones), zeroA nM1, addA nM1 (2 * wA) nOne, zeroA nD,
  subA nD aN (2 * wX), divmod nD nRem nM1 nDt, zeroA nZ] ++ eqA nRem nZ ++ [.block andZero])

/-! ## `b² - 4 n` -/

def nB : Nat := 6
def nBy : Nat := 7
def wB : Nat := 5
def wSq : Nat := 6
def wX4 : Nat := 7

/-- `b = q + 1` (narrow, and its copy), and `b²` into wide array 6. -/
def square : Prog isa := seqs [.block ones, zeroA nB, addA nB nD nOne, zeroA nBy, copyA nBy nB,
  .block setWid, zeroA wB, zeroA wSq, .block setNar, copyA (2 * wB) nB, product nBy wB wSq wT]

/-- `b² - 4 n` into wide array 7, and `b² ≥ 4 n` and `b² - 4 n ≥ 1` and'ed
into the mask. -/
def minus4n : Prog isa := seqs ([.block setWid, dblA wN c0 [], dblA wN c0 [], subA wX4 wSq wN, .block andMask] ++
  oneA wOne ++ [subA wT wX4 wOne, .block andMask])

/-! ## The square root

`32 W` steps, two bits of the wide `[7]` at a time from its top: the
remainder (2) takes them, and the root (4) a bit, one if `4 y + 1` (5) fits
in the remainder. -/

def nRm : Nat := 2
def nY : Nat := 4
def nTy : Nat := 5
def nDf : Nat := 3

def sqrtBody : Prog isa := seqs [
  .block setWid, dblA wX4 c0 (cTo .x1), dblA wX4 c0 (cTo .x2), .block setNar,
  dblA nRm (cOf .x1) [], dblA nRm (cOf .x2) [],
  copyA nTy nY, dblA nTy c0 [], dblA nTy c1 [],
  subA nDf nRm nTy, selA nRm nDf, dblA nY [.adds .x .x3 .x15 .x15] [],
  .block [.subImm .x .x6 .x6 1]]

/-- `32 W = 64 (v + 1)` steps into `x6`. -/
def countS : List Instr := ws ++ [.addImm .x .x6 .x12 1, .lsl .x .x6 .x6 6]

def sqrt : Prog isa := seqs ([.block setNar, zeroA nRm, zeroA nY, .block countS, .loop sqrtBody (.nonzero .x .x6),
  zeroA nZ] ++ eqA nRm nZ ++ [.block andZero])

/-! ## The factors -/

def nP : Nat := 8
def nQ : Nat := 9

def factors : List (Prog isa) := [.block ones, zeroA nP, addA nP nB nY, halfA nP nP, zeroA nQ, subA nQ nB nY,
  halfA nQ nQ] ++ storeA nP sP sK sMask ++ storeA nQ sQ sK sMask ++ [.block retMask]

/-! ## The function -/

/-- The computation, once `n` is known valid. -/
def main : Prog isa := seqs ([.block (Keys.head ++ setNar)] ++ loadA aN sN sK ++ loadA aE sE sElen ++
  loadA aD sD sDl ++ prod ++ [deMinus, twos, gcd, aProd, divA, divB, square, minus4n, sqrt] ++ factors)

/-- `vg_rsa_recover_primes_det`. -/
def code : Prog isa := .seq (.block (entry ++ invalid)) (.ite (.zero .x .x9) fail main)

end VG.Impl.Rsa.AArch64.RecoverDet
