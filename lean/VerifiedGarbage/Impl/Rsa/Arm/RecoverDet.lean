module

public import VerifiedGarbage.Impl.Rsa.Arm.Recover

/-! # RSA prime recovery by SP 800-56B Rev. 2 Appendix C.2 on ARMv7

`vg_rsa_recover_primes_det` has `vg_rsa_recover_primes`' signature, frame,
entry and exits (`Recover.codeWith`), its loads and the product `M = d e`
(`Recover.loads`, `Recover.prod`), and its stores of the factors under the
mask (`Recover.stores`), in the key working space with `w` words
(narrow) and `W = 2 w + 2` words (wide, whose array `j` is the narrow arrays
`2 j` and `2 j + 1`). Between them, Appendix C.2 without a branch on a
secret:

* `x = d e - 1` (wide), and whether `d e ≥ 2` (`sOkDE`);
* `32 w` steps that halve `u = n - 1` while it is even, and while the low
  half of `x` (narrow) is even too halve it and double the wide `x`
  (`twosBody`): `u` odd and `gcd(n - 1, x) = 2^k gcd(u, x / 2^k)`;
* `gcd(u, x / 2^k)` by `inverse`, at the width `w`, with the odd modulus
  `u` (`1` where `u = 1`, which `inverse` does not take);
* `a = (2^k x) gcd(u, x / 2^k)` by the `32 w` bits of the GCD
  (`product`);
* `m = ⌊a / n⌋` and `r = a mod n` (the division on the wide arrays), whether
  `m < n`, and `b - 1 = (n - r) / (m + 1)` with its remainder (on the narrow
  arrays; a divisor `m + 1` that is zero modulo `2^(32 w)`, which only
  `m ≥ n` gives, is replaced by 1);
* `b² - 4 n` (`product` again), whether it is positive, and its integer
  square root two bits at a time from the top (`sqrtBody`), with the
  remainder;
* `p = (b + ϒ) / 2` and `q = (b - ϒ) / 2`, written under the mask of every
  check.

Sums are differences with a negation (`add`). Every loop's count is a
public length, and every address is computed from `r7`, `r8` and `r9`.
-/

@[expose] public section

namespace VG.Impl.Rsa.Arm.RecoverDet
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Rsa.Arm.Keys
open VG.Impl.Rsa.Arm.Recover (ctxw clrW aW)

/-! ## Header words

Bytes 0–19 are the division's (16: `w`), 100–112 the shared routines', and
132 the mask of the result. -/

/-- `d e < 1`, `d e - 1 < 1`, and `d e ≥ 2`. -/
def sB0 : Nat := 20
def sB1 : Nat := 24
def sOkDE : Nat := 28
/-- A step of the halvings: `u` odd, the narrow `x` odd, `u` even, both even. -/
def sU : Nat := 32
def sX : Nat := 36
def sEven : Nat := 40
def sBoth : Nat := 44
/-- A product's multiplier bit. -/
def sY : Nat := 48
/-- `m < n`, `(n - r) mod (m + 1) = 0`. -/
def sLt : Nat := 52
def sExact : Nat := 56
/-- `b² < 4 n`, `b² - 4 n < 1`, and `b² > 4 n`. -/
def sC1 : Nat := 60
def sC2 : Nat := 64
def sOk4 : Nat := 68
/-- The square root's borrow. -/
def sBb : Nat := 72
/-- The remainder of the square root is zero. -/
def sOk5 : Nat := 76
/-- A loop's count. -/
def sK : Nat := 80
/-- `u = 1`. -/
def sU1 : Nat := 84
/-- `m + 1` is zero modulo `2^(32 w)`. -/
def sM0 : Nat := 88
def sMask : Nat := VG.Impl.Rsa.Arm.Recover.sMask

/-! ## Arrays

Wide: `d e` (`Recover.wM`), zero, one, `x`, `2^k x`, two temporaries, the
product, `n` widened, the remainder, the division's temporary and `b`
widened. -/

def wZ : Nat := 14
def wOne : Nat := 13
def wX : Nat := 10
def wX3 : Nat := 11
def wT1 : Nat := 12
def wT2 : Nat := 15
def wA : Nat := 9
def wN : Nat := 17
def wR : Nat := 19
def wDt : Nat := 18
def wB : Nat := 10

/-- Narrow: `n` (`Recover.aN`), zero, one, two temporaries, `u` (the GCD's
modulus `aM`), the halved `x` (the low half of `wX`), the GCD's input and
result, the multiplier of the first product, `m mod 2^(32 w)` (the low half
of `wA`), `m + 1`, `n - r` (then the quotient), `r mod 2^(32 w)` (the low
half of `wR`), the division's remainder and temporary, `b`, its copy for the
second product, and the square root's remainder, root, `4 y + 1` and
difference. -/
def aN : Nat := VG.Impl.Rsa.Arm.Recover.aN
def aZN : Nat := 40
def aOneN : Nat := 41
def aT1 : Nat := 36
def aT2 : Nat := 37
def aU : Nat := 8
def aX2 : Nat := 20
def aGx : Nat := 0
def aG1 : Nat := 1
def aG : Nat := 34
def aMlo : Nat := 18
def aM1 : Nat := 22
def aD : Nat := 24
def aRlo : Nat := 38
def aRem : Nat := 2
def aDt : Nat := 3
def aB : Nat := 4
def aBy : Nat := 5
def aRm : Nat := 6
def aY : Nat := 7
def aTy : Nat := 0
def aDf : Nat := 1
/-- The factors, as `Recover.stores` takes them. -/
def aP : Nat := 5
def aQ : Nat := 6

/-! ## Small operations -/

/-- The slot `d` := `r11` (a borrow). -/
def brw (d : Nat) : List Instr := [.str .r11 .r8 d]

/-- The slot `d` := the slot `a` negated (a bit). -/
def notS (d a : Nat) : List Instr := [.ldr .r1 .r8 a, .dp .eor .r1 .r1 (.imm 1), .str .r1 .r8 d]

/-- The slot `d` := neither the slot `a` nor `b` (bits). -/
def norS (d a b : Nat) : List Instr :=
  [.ldr .r1 .r8 a, .ldr .r2 .r8 b, .dp .orr .r1 .r1 (.reg .r2), .dp .eor .r1 .r1 (.imm 1), .str .r1 .r8 d]

/-- From the narrow arrays to the wide ones: `r9 := 2 r9 + 2` and its
stride, from registers alone. -/
def toW : List Instr := [.mov .r9 (.shifted .r9 .lsl 1), .dp .add .r9 .r9 (.imm 2)] ++ stride

/-- From the wide arrays to the narrow ones: `r9 := (r9 - 2) / 2`. -/
def toN : List Instr := [.dp .sub .r9 .r9 (.imm 2), .mov .r9 (.shifted .r9 .lsr 1)] ++ stride

/-- `r11 := 0`. -/
def clr11 : List Instr := [.mov .r11 (.imm 0)]

/-- `[j] := 2 [j] + r11` modulo the width, the bit shifted out in `r11`. -/
def shl (j : Nat) : Prog isa := .seq (.block (ptr .r0 j ++ [.mov .lr (.reg .r9)])) shiftLeft

/-- `[o] := [a] + [b]` modulo the width, through `t`: `[a] - (0 - [b])`. -/
def add (o a b t z : Nat) : Prog isa := .seq (sub3 t z b) (sub3 o a t)

/-- A count of `2^e` times the width in `r9` into `sK`. -/
def cntInit (e : Nat) : List Instr := [.mov .r1 (.shifted .r9 .lsl e), .str .r1 .r8 sK]

/-- The count less one, and Z if it is zero. -/
def cntNext : List Instr := [.ldr .r1 .r8 sK, .subs .r1 .r1 (.imm 1), .str .r1 .r8 sK]

/-! ## `d e - 1` -/

def deMinus : Prog isa := seqs [sub3 wZ VG.Impl.Rsa.Arm.Recover.wM VG.Impl.Rsa.Arm.Recover.wM,
  copy wOne wZ, .block (setOne wOne),
  sub3 wX VG.Impl.Rsa.Arm.Recover.wM wOne, .block (brw sB0),
  sub3 wT1 wX wOne, .block (brw sB1 ++ norS sOkDE sB0 sB1)]

/-! ## The halvings -/

/-- Zero and one narrow, `u = n - 1`, and `2^k x := x`. -/
def twosInit : Prog isa := seqs [copy wX3 wX, .block toN, sub3 aZN aN aN, copy aOneN aZN,
  .block (setOne aOneN), sub3 aU aN aOneN]

/-- `[j]` halved if the slot `sl` holds 1, through `aT1` and `aT2`. -/
def halfIf (j sl : Nat) : Prog isa :=
  seqs [copy aT1 j, copy aT2 j, .block clr11, half aT2, sel j aT1 aT2 sl]

def twosFlags : List Instr := bitOf sU aU ++ bitOf sX aX2 ++ notS sEven sU ++ norS sBoth sU sX

def twosBody : Prog isa := seqs [.block twosFlags, halfIf aU sEven, halfIf aX2 sBoth,
  .block toW, copy wT1 wX3, copy wT2 wX3, .block clr11, shl wT2, sel wX3 wT1 wT2 sBoth,
  .block (toN ++ cntNext)]

def twosPre : Prog isa := .seq twosInit (.block (cntInit 5))

def twos : Prog isa := .seq twosPre (.loop twosBody .ne)

/-! ## The GCD -/

/-- `gcd(u, x / 2^k)` into `aG`: `inverse`'s, or 1 where `u = 1`. -/
def gcdPost : Prog isa := .seq (eqS sU1 aU aOneN aW) (sel aG aG1 aOneN sU1)

def gcd : Prog isa := seqs [copy aGx aX2, inverse, gcdPost]

/-! ## Products: `[a] := [y] [x]` modulo `2^(32 W)`, by the `32 w` bits of
the narrow `[y]`, `[x]` doubled at each, through `[t]` and `[t2]`, with `[z]`
zero (wide). -/

def productStep (y x a t t2 z : Nat) : Prog isa := seqs [.block (bitOf sY y ++ toW), sel t z x sY,
  add t a t t2 z, copy a t, .block clr11, shl x, .block (toN ++ clr11), half y, .block cntNext]

/-- From the narrow context, back to it. -/
def productPre (a z : Nat) : Prog isa := seqs [.block toW, copy a z, .block (toN ++ cntInit 5)]

def product (y x a t t2 z : Nat) : Prog isa := .seq (productPre a z) (.loop (productStep y x a t t2 z) .ne)

/-! ## The divisions -/

/-- The wide division's header: `W` as its count, and its arrays. -/
def divHdrW : List Instr := [.str .r9 .r8 16] ++ VG.Impl.Rsa.Arm.CrtValues.divHdr wA wR wN wDt

/-- `w = (W - 2) / 2` back in the header, and the narrow context. -/
def restoreW : List Instr :=
  [.ldr .r9 .r8 16, .dp .sub .r9 .r9 (.imm 2), .mov .r9 (.shifted .r9 .lsr 1), .str .r9 .r8 16] ++ stride

/-- `n` widened; `m` and `r`, and whether `m < n`. -/
def divAPre : Prog isa := seqs [.block toW, copy wN wZ, .block toN, copy (2 * wN) aN,
  .block (toW ++ clrW wN ++ divHdrW)]

def divAPost : Prog isa := seqs [.block toW, sub3 wT1 wA wN, .block (brw sLt ++ toN)]

def divA : Prog isa := seqs [divAPre, Rsa.Arm.Div.code, .block restoreW, divAPost]

/-- `m + 1` (1 where it is zero modulo `2^(32 w)`, so that the divisor is
positive), `n - r`, their quotient and remainder, and whether it is zero. -/
def divBPre : Prog isa := seqs [sub3 aT2 aZN aOneN, sub3 aT1 aMlo aT2, eqS sM0 aT1 aZN aW,
  sel aM1 aT1 aOneN sM0, sub3 aD aN aRlo,
  .block (clrW aM1 ++ VG.Impl.Rsa.Arm.CrtValues.divHdr aD aRem aM1 aDt)]

def divB : Prog isa := seqs [divBPre, Rsa.Arm.Div.code, .block ctxw, eqS sExact aRem aZN aW]

/-! ## `b² - 4 n` -/

/-- `b = q + 1`, narrow in `aB` and `aBy` and wide in `wB`, and `b²` in `wA`. -/
def squarePre : Prog isa := seqs [sub3 aT1 aZN aOneN, sub3 aB aD aT1, copy aBy aB,
  .block toW, copy wB wZ, .block toN, copy (2 * wB) aB]

def square : Prog isa := .seq squarePre (product aBy wB wA wT1 wT2 wZ)

/-- `4 n`, `b² - 4 n` in `wR`, and whether `b² > 4 n`. -/
def minus4n : Prog isa := seqs [.block (toW ++ clr11), shl wN, .block clr11, shl wN,
  sub3 wR wA wN, .block (brw sC1), sub3 wT1 wR wOne, .block (brw sC2 ++ norS sOk4 sC1 sC2 ++ toN)]

/-! ## The square root

`16 W` steps, two bits of the wide `[wR]` at a time from its top: the
remainder `[aRm]` takes them, and the root `[aY]` a bit, one if `4 y + 1`
fits in the remainder. -/

def sqrtBody : Prog isa := seqs [
  .block (toW ++ clr11), shl wR, .block toN, shl aRm,
  .block (toW ++ clr11), shl wR, .block toN, shl aRm,
  copy aTy aY, .block clr11, shl aTy, .block [.mov .r11 (.imm 1)], shl aTy,
  sub3 aDf aRm aTy, .block (brw sBb), copy aT1 aRm, sel aRm aDf aT1 sBb,
  .block [.ldr .r11 .r8 sBb, .dp .eor .r11 .r11 (.imm 1)], shl aY, .block cntNext]

def sqrtPre : Prog isa := seqs [copy aRm aZN, copy aY aZN, .block (toW ++ cntInit 4 ++ toN)]

def sqrt : Prog isa := seqs [sqrtPre, .loop sqrtBody .ne, eqS sOk5 aRm aZN aW]

/-! ## The factors -/

def factors : Prog isa := seqs [add aP aB aY aT1 aZN, .block clr11, half aP,
  sub3 aQ aB aY, .block clr11, half aQ,
  .block (andS sMask sOkDE sLt ++ andS sMask sMask sExact ++ andS sMask sMask sOk4 ++
    andS sMask sMask sOk5)]

/-! ## The function -/

def det : Prog isa := seqs [deMinus, twos, gcd, product aG wX3 wA wT1 wT2 wZ, divA, divB,
  square, minus4n, sqrt, factors]

/-- Once `n` is known valid. -/
def valid : Prog isa := seqs [VG.Impl.Rsa.Arm.Recover.loads, VG.Impl.Rsa.Arm.Recover.prod, det,
  VG.Impl.Rsa.Arm.Recover.stores]

/-- `vg_rsa_recover_primes_det`. -/
def code : Prog isa := VG.Impl.Rsa.Arm.Recover.codeWith (.ite .eq valid VG.Impl.Rsa.Arm.Recover.fail)

end VG.Impl.Rsa.Arm.RecoverDet
