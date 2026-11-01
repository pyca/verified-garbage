module

public import VerifiedGarbage.Impl.Rsa.X86.RecoverRt

/-! # RSA prime recovery by SP 800-56B Rev. 2 Appendix C.2 at a run-time width (i686)

`RecoverRt`'s working space, arrays and inputs (`loads`, `prod`: `d e` in
the wide array `wM`), then Appendix C.2 without a branch on a secret:

* `x = d e - 1` (`wX`), and whether `d e ≥ 2` (`sOkDE`);
* the odd part `u` of `n - 1` and `gcd(n - 1, x) = 2^k gcd(u, x)`: `32 w`
  steps that halve `u` while it is even, and while `x` is even too halve it
  and double `x` (`twosBody`), then the batched GCD of `u` and the halved
  `x`;
* `a = (2^k x) gcd(u, x)` (`product`, by the bits of the GCD);
* `m = ⌊a / n⌋` and `r = a mod n` (`KeyRt.div` on the wide arrays), and
  `b - 1 = (n - r) / (m + 1)` (`KeyRt.div` on the narrow arrays);
* `b² - 4 n` and its integer square root, two bits at a time from the top
  (`sqrtBody`), with the remainder;
* `p = (b + ϒ) / 2` and `q = (b - ϒ) / 2`, written under the mask of every
  check (`RecoverRt.stores`).

Every loop's count is a public length.
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.RecoverDetRt
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Bignum.X86
open VG.Impl.Rsa.X86.Keys (seqs aZero)
open VG.Impl.Rsa.X86.KeyRt (arrPtr bytesB copy sel sub3 half bitOf setOne orOne chain addLow
  zeroWide eqSFast div bits)
open VG.Impl.Rsa.X86.RecoverRt (nar wid flagNot flagBin)

/-! ## Header words

The batched GCD writes the header words 16 to 100, and the division 136 and
140; the flags that live across the GCD are above them. -/

/-- `d e < 1` and `d e - 1 < 1`. -/
def sB0 : Nat := 116
def sB1 : Nat := 120
/-- `d e ≥ 2`. -/
def sOkDE : Nat := 144
/-- A step of the halvings: `u` odd, `x` odd, both even, `u` even. -/
def sU : Nat := 116
def sX : Nat := 120
def sBoth : Nat := 124
def sEven : Nat := 128
/-- A product's multiplier bit. -/
def sY : Nat := 116
/-- `m < n`. -/
def sLt : Nat := 16
/-- `(n - r) mod (m + 1) = 0`. -/
def sExact : Nat := 20
/-- `b² < 4 n`, `b² - 4 n < 1`, and `b² > 4 n`. -/
def sC1 : Nat := 24
def sC2 : Nat := 28
def sOk4 : Nat := 32
/-- The square root's two bits, its borrow and its bit. -/
def sHi : Nat := 36
def sLo : Nat := 40
def sBb : Nat := 44
def sNb : Nat := 48
/-- The remainder of the square root is zero. -/
def sOk5 : Nat := 52
/-- A loop's count, from a public length. -/
def sK : Nat := 148

/-- `32 w` and `32 W / 2` steps into `sK`. -/
def countN : List Instr := bits nar ++ [.store (sc sK) .esi]
def countW : List Instr := bits wid ++ [.shift .shr .esi 1, .store (sc sK) .esi]

/-- The count less one, and ZF if it is zero. -/
def countNext : List Instr := [.mov .eax (.mem (sc sK)), .alu .sub .eax (.imm 1), .store (sc sK) .eax]

/-! ## Arrays

Narrow arrays (`nar`) are numbered as in `RecoverRt`; wide array `j` (`wid`)
is narrow arrays `2 j` and `2 j + 1`. -/

/-- Wide: one, `x`, `2^k x`, a temporary, a zero, the product, `n`, the
remainder and the division's temporary. -/
def wOne : Nat := 9
def wX : Nat := 10
def wX3 : Nat := 13
def wT : Nat := 14
def wOne2 : Nat := 21
def wA : Nat := 17
def wZ2 : Nat := 18
def wN : Nat := 19
def wR : Nat := 20
def wDt : Nat := 21
/-- The multiplicand `b`, wide. -/
def wB : Nat := 9

/-- Narrow: zero (the low half of the wide zero), `x` halved, one, `u`, a
temporary, `n`. -/
def aZ0 : Nat := 0
def aX2 : Nat := 20
def aOneN : Nat := 22
def aU : Nat := 24
def aTmp : Nat := 30
def aN : Nat := VG.Impl.Rsa.X86.Recover.aN
/-- The GCD's inputs and result. -/
def aGm : Nat := 8
def aGx : Nat := 0
def aG : Nat := 1
/-- After the product: the quotient's low half, one, `m + 1`, `n - r` (then
`b - 1` and `b`), the remainder's low half and the division's remainder and
temporary; the multiplier `b`. -/
def aM : Nat := 34
def aOne1 : Nat := 26
def aM1 : Nat := 28
def aD : Nat := 30
def aRlo : Nat := 40
def aRem : Nat := 2
def aDt : Nat := 42
def aBy : Nat := 12
/-- The square root: remainder, root, `4 y + 1`, difference. -/
def aRm : Nat := 2
def aY : Nat := 4
def aTy : Nat := 6
def aDf : Nat := 8
/-- The factors, as `RecoverRt.stores` takes them. -/
def aP : Nat := 5
def aQ : Nat := 6

/-! ## `d e - 1` -/

/-- A wide array zeroed with its extra word, then its low word one. -/
def wideOne (j : Nat) : Prog isa := .seq (zeroWide wid j) (.block (setOne wid j))

def deMinus : Prog isa := seqs [wideOne wOne,
  sub3 wid wX VG.Impl.Rsa.X86.Recover.wM wOne, .block [.store (sc sB0) .ebx],
  sub3 wid wT wX wOne, .block [.store (sc sB1) .ebx],
  flagBin .or sOkDE sB0 sB1, flagNot sOkDE sOkDE]

/-! ## The halvings -/

/-- `u = n - 1`, `x` halved in `aX2` (the low half of `wX`), `2^k x` in `wX3`. -/
def twosInit : Prog isa := seqs [copy nar aOneN aZ0, .block (setOne nar aOneN),
  sub3 nar aU aN aOneN, copy wid wX3 wX]

/-- `[j]` halved if the header word `sl` is one, through `aTmp`. -/
def halfIf (j sl : Nat) : Prog isa := seqs [copy nar aTmp j, .block [.mov .ebx (.imm 0)], half nar aTmp,
  sel nar j j aTmp sl]

def twosFlags : Prog isa := seqs [.block (bitOf nar sU aU), .block (bitOf nar sX aX2),
  flagBin .or sBoth sU sX, flagNot sBoth sBoth, flagNot sEven sU]

def twosBody : Prog isa := seqs [twosFlags, halfIf aU sEven, halfIf aX2 sBoth,
  chain wid .adc wT wX3 wX3 false, sel wid wX3 wX3 wT sBoth, .block countNext]

def twos : Prog isa := seqs [twosInit, .block countN, .loop twosBody .ne]

/-! ## The GCD -/

def gcdSet : Prog isa := seqs [copy nar aGm aU, copy nar aGx aX2]

/-! ## Products: `[a] += [y] [x]` by the `32 w` bits of the narrow `[y]`,
`[x]` doubled at each, through `[t]`, with `[z]` zero (wide). -/

def productStep (y x a t z : Nat) : Prog isa := seqs [.block (bitOf nar sY y), sel wid t z x sY,
  chain wid .adc a a t false, chain wid .adc x x x false, .block [.mov .ebx (.imm 0)], half nar y,
  .block countNext]

def product (y x a t z : Nat) : Prog isa := .seq (.block countN) (.loop (productStep y x a t z) .ne)

/-- `a = 2^k x gcd(u, x)`: the GCD's result times `wX3`. -/
def aProduct : Prog isa := seqs [zeroWide wid wZ2, zeroWide wid wA, product aG wX3 wA wT wZ2]

/-! ## The divisions -/

/-- `n` wide, its extra word zero: the wide `wN` zeroed, then its low half `n`. -/
def wideN : Prog isa := .seq (zeroWide wid wN) (copy nar (2 * wN) aN)

/-- The word above narrow array `j`'s number zeroed. -/
def zeroAbove (j : Nat) : List Instr := arrPtr nar .eax j .edx ++
  [.alu .add .eax (.reg .edx), .alu .sub .eax (.imm 8), .mov .ecx (.imm 0), .store (at_ .eax 0) .ecx]

/-- `m` and `r`, and whether `m < n`. -/
def divA : Prog isa := seqs [wideN, div wid wA wR wN wDt,
  sub3 wid wT wA wN, .block [.store (sc sLt) .ebx]]

/-- `m + 1`, `n - r`, their quotient and remainder, and whether it is zero. -/
def divB : Prog isa := seqs [copy nar aOne1 aZero, .block (setOne nar aOne1),
  chain nar .adc aM1 aM aOne1 false, .block (zeroAbove aM1),
  sub3 nar aD aN aRlo, div nar aD aRem aM1 aDt, eqSFast nar sExact aRem aZero]

/-! ## `b² - 4 n` -/

/-- `b`, narrow in `aD` and `aBy` and wide in `wB`, and `b²` in `wA`. -/
def square : Prog isa := seqs [chain nar .adc aD aD aOne1 false, copy nar aBy aD,
  zeroWide wid wB, copy nar (2 * wB) aD, zeroWide wid wA, product aBy wB wA wT wZ2]

/-- `b² - 4 n` in `wR`, and whether `b² > 4 n`. -/
def minus4n : Prog isa := seqs [chain wid .adc wN wN wN false, chain wid .adc wN wN wN false,
  wideOne wOne2, sub3 wid wR wA wN, .block [.store (sc sC1) .ebx],
  sub3 wid wT wR wOne2, .block [.store (sc sC2) .ebx],
  flagBin .or sOk4 sC1 sC2, flagNot sOk4 sOk4]

/-! ## The square root

`32 W / 2` steps, two bits of `[wR]` at a time from its top: the remainder
`[aRm]` takes them, and the root `[aY]` a bit, one if `4 y + 1` fits in the
remainder. -/

/-- The carry of a chain (`ecx` a mask) into the header word `sl`. -/
def carryTo (sl : Nat) : List Instr := [.mov .eax (.reg .ecx), .alu .and .eax (.imm 1), .store (sc sl) .eax]

def sqrtBody : Prog isa := seqs [
  chain wid .adc wR wR wR false, .block (carryTo sHi), chain nar .adc aRm aRm aRm false, .block (addLow nar aRm sHi),
  chain wid .adc wR wR wR false, .block (carryTo sLo), chain nar .adc aRm aRm aRm false, .block (addLow nar aRm sLo),
  chain nar .adc aTy aY aY false, chain nar .adc aTy aTy aTy false, .block (orOne nar aTy),
  sub3 nar aDf aRm aTy, .block [.store (sc sBb) .ebx], flagNot sNb sBb,
  sel nar aRm aDf aRm sBb,
  chain nar .adc aY aY aY false, .block (addLow nar aY sNb), .block countNext]

def sqrt : Prog isa := seqs [copy nar aRm aZero, copy nar aY aZero,
  .block countW, .loop sqrtBody .ne, eqSFast nar sOk5 aRm aZero]

/-! ## The factors -/

def factors : Prog isa := seqs [
  chain nar .adc aP aD aY false, .block [.mov .ebx (.imm 0)], half nar aP,
  sub3 nar aQ aD aY, .block [.mov .ebx (.imm 0)], half nar aQ,
  flagBin .and VG.Impl.Rsa.X86.Recover.sMask sOkDE sLt, flagBin .and VG.Impl.Rsa.X86.Recover.sMask VG.Impl.Rsa.X86.Recover.sMask sExact,
  flagBin .and VG.Impl.Rsa.X86.Recover.sMask VG.Impl.Rsa.X86.Recover.sMask sOk4,
  flagBin .and VG.Impl.Rsa.X86.Recover.sMask VG.Impl.Rsa.X86.Recover.sMask sOk5]

/-! ## The function -/

def det : Prog isa := seqs [deMinus, twos, gcdSet, VG.Impl.Rsa.X86.GcdBatchRt.body wid, aProduct, divA, divB,
  square, minus4n, sqrt, factors]

def sized : Prog isa := seqs [VG.Impl.Rsa.X86.RecoverRt.loads, VG.Impl.Rsa.X86.RecoverRt.prod, det,
  VG.Impl.Rsa.X86.RecoverRt.stores]

def body : Prog isa := .seq
  (.block (VG.Impl.Rsa.X86.CrtValues.inputArgs 4)) (.seq (.block modulusCheck) (.ite .e sized VG.Impl.Rsa.X86.Recover.failure))

def code : Prog isa := .seq (.block VG.Impl.Rsa.X86.Recover.entry) (.seq body (.block PublicFn.restore))

end VG.Impl.Rsa.X86.RecoverDetRt
