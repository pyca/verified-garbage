module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.Recover
public import VerifiedGarbage.Impl.Rsa.PPC64LE.InvBatch

/-! # `vg_rsa_recover_primes_det` on PPC64LE

SP 800-56B Rev. 2 Appendix C.2 without a branch on a secret, in
`vg_rsa_recover_primes`' working space, entry, loads, product `d e` and
stores (`Impl/Rsa/PPC64LE/Recover.lean`): the numbers are `w` digits
(narrow) or, in the same working space read with `W = 2 w + 2` digits, wide,
wide array `j` being the narrow arrays `2 j` and `2 j + 1`. A narrow number
copied into the low half of a wide array of zeros is that wide number.

* `x = d e - 1` (wide), and whether `d e ≥ 2`;
* `32 w` steps that halve `u = n - 1` while it is even, and while `x` is even
  too halve it and double `2^k x` (all wide), then `gcd(u, x)` by the
  batched divstep inverse (`InvBatch.inverse`, on narrow arrays), with 1
  where `u = 1`, which the inverse leaves to its caller;
* `a = (2^k x) gcd(u, x)` modulo `2^(32 W)` by the `32 w` bits of the GCD,
  doubling the multiplicand (`product`), and `m = ⌊a / n⌋`, `r = a mod n`
  (`Div.div`, wide);
* `b - 1 = (n - r) / (m + 1)` (`Div.div`, narrow), `b²` (`product`) and
  `b² - 4 n`;
* its square root, two bits at a time from the top in `16 W` steps (`sqrtBody`):
  the wide radicand shifted left into the narrow remainder (`shlC`, whose
  carry in is `r9`), which keeps `4 y + 1` where it fits;
* `p = (b + ϒ) / 2` and `q = (b - ϒ) / 2`, written under the mask of every
  check (`Recover.stores`).

Each loop counts down in `r27`, set from `w`; the operations keep it. The
addresses and branches depend only on `w` and the base, as in the
operations of the key working space (`KeyWs.lean`).
-/

@[expose] public section

namespace VG.Impl.Rsa.PPC64LE.RecoverDet

open VG.PPC64LE VG.Impl.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Recover (ctxW ctxw clrW)

/-! ## The header's slots

Bytes 0–55 are the function's slots; 124–132 are the shared routines' and
152 the mask (`Recover.sMask`). -/

/-- `d e < 1` and `d e - 1 < 1`. -/
def sB0 : Nat := 0
def sB1 : Nat := 4
/-- A step of the halvings: the low bits of `u` and `x`, `u` even, and both even. -/
def sU : Nat := 8
def sX : Nat := 12
def sEven : Nat := 16
def sBoth : Nat := 20
/-- A product's multiplier bit. -/
def sY : Nat := 24
/-- `m < n`. -/
def sLt : Nat := 28
/-- `(n - r) mod (m + 1) = 0`. -/
def sExact : Nat := 32
/-- `b² < 4 n` and `b² - 4 n < 1`. -/
def sC1 : Nat := 36
def sC2 : Nat := 40
/-- The square root's borrow. -/
def sBb : Nat := 44
/-- The square root's remainder is zero. -/
def sOk5 : Nat := 48
/-- `u = 1`. -/
def sU1 : Nat := 52

/-! ## The arrays

Wide: zero (from the loads), `d e` (`Recover.wM`), one, `x`, a temporary,
`2^k x`, `x` halved, `u` (later `b`), zero, the multiplier, the product, the
remainder, `n`, the division's temporary, and the negated addend. -/

def wZ : Nat := 0
def wDE : Nat := 3
def wOne : Nat := 9
def wX : Nat := 10
def wT : Nat := 11
def wX3 : Nat := 12
def wX2 : Nat := 13
def wU : Nat := 14
def wZero : Nat := 15
def wY : Nat := 8
def wA : Nat := 17
def wR : Nat := 18
def wN : Nat := 19
def wDt : Nat := 21
def wNg : Nat := 20

/-- Narrow: `n` (`Recover.aN`), the low halves of the wide arrays, one, and
the inverse's input `x` (array 0), modulus (array 8) and GCD (array 1). -/
def aN : Nat := 32
def aX : Nat := 20
def aX2 : Nat := 26
def aU : Nat := 28
def aZero : Nat := 30
def aY : Nat := 16
def aM : Nat := 34
def aRlo : Nat := 36
def aWN : Nat := 38
def aOne : Nat := 42
def aGx : Nat := 0
def aGm : Nat := 8
def aG : Nat := 1
/-- The second division: one, `-1`, `m + 1`, `n - r` (then `b - 1` and `b`),
its remainder and temporary; `b` into the low half of `wU`. -/
def aOne2 : Nat := 22
def aNeg1 : Nat := 23
def aM1 : Nat := 24
def aD : Nat := 25
def aRem : Nat := 26
def aDt : Nat := 27
/-- The square root: remainder, root, `4 y + 1`, difference; `-y`; the factors. -/
def aRm : Nat := 2
def aSy : Nat := 4
def aTy : Nat := 6
def aDf : Nat := 8
def aNy : Nat := 9
def aP : Nat := 5
def aQ : Nat := 6

/-! ## Operations -/

/-- `[j] := 2 [j] + r9` modulo `2^(32 w)`, for `r9` 0 or 1, the bit shifted
out in `r9`. -/
def shlC (j : Nat) : Prog isa :=
  .seq (.block (ptr .r5 j))
    (evenW (.seq (.block [.lsr .d .r8 .r29 1]) (countLoop .r8 Div.shlWBody))
      (.seq (.block [.addi .r8 .r29 0]) (countLoop .r8 Div.shlBody)))

/-- `[j] := 2 [j]` modulo `2^(32 w)`, the bit shifted out in `r9`. -/
def shl (j : Nat) : Prog isa := .seq (.block [.li .r9 0]) (shlC j)

/-- `[o] := [a] + [b]` modulo `2^(32 w)`, through `[t] = [z] - [b]`, with
`[z]` zero. -/
def add (o a b z t : Nat) : Prog isa := .seq (sub3 t z b) (sub3 o a t)

/-- `32 w` steps into `r27`, from `w`. -/
def countN : List Instr := [.lsl .r27 .r29 5]

/-- `16 W = 32 w + 32` steps into `r27`, from `w`. -/
def countS : List Instr := [.lsl .r27 .r29 5, .addi .r27 .r27 32]

/-- A step less. -/
def next : List Instr := [.subi .r27 .r27 1]

/-! ## `d e - 1` (wide) -/

/-- One (`wOne`), `x = d e - 1`, and the borrows of `d e - 1` and `x - 1`;
the zero `wZero`, which the inverse leaves alone. -/
def deMinus : Prog isa := seqs [copy wOne wZ, .block (setOne wOne),
  sub3 wX wDE wOne, .block (stBorrow sB0), sub3 wT wX wOne, .block (stBorrow sB1), copy wZero wZ]

/-! ## The halvings -/

/-- `2^k x := x`, `x` and `u = n - 1` into zeroed wide arrays (through the
narrow view), the multiplier's wide array zeroed, and `32 w` steps. -/
def twosInit : Prog isa := seqs [copy wX3 wX, copy wX2 wZero, copy wU wZero, copy wY wZero,
  .block ctxw, copy aX2 aX, copy aOne aZero, .block (setOne aOne), sub3 aU aN aOne,
  .block (countN ++ ctxW)]

/-- The flags of a step: `even := ¬u₀` and `both := ¬u₀ ∧ ¬x₀`. -/
def twosFlags : List Instr :=
  bitOf sU wU ++ bitOf sX wX2 ++
  [.load .w .r0 .r31 sU, .load .w .r3 .r31 sX, .li .r5 1, .logic .xor .r0 .r0 .r5,
    .logic .xor .r3 .r3 .r5, .store .w .r0 .r31 sEven, .logic .and .r3 .r3 .r0, .store .w .r3 .r31 sBoth]

/-- `[j]` halved if the slot `sl` holds 1, through `wT`. -/
def halfIf (j sl : Nat) : Prog isa := seqs [copy wT j, .block [.li .r9 0], half wT, sel j j wT sl]

def twosBody : Prog isa := seqs [.block twosFlags, halfIf wU sEven, halfIf wX2 sBoth,
  copy wT wX3, shl wT, sel wX3 wX3 wT sBoth, .block next]

def twos : Prog isa := seqs [twosInit, .loop twosBody (.nonzero .d .r27)]

/-! ## The GCD (narrow) -/

/-- `gcd(u, x)` into array 1: the inverse's inputs, `n = w`, and 1 where
`u = 1`. Then the GCD into the low half of `wY`. -/
def gcd : Prog isa := seqs [.block ctxw, copy aGx aX2, copy aGm aU, .block [.addi .r11 .r29 0],
  InvBatch.inverse, eqS sU1 aGm aOne, sel aG aG aOne sU1, copy aY aG]

/-! ## Products: `[a] := [y] [x]` modulo `2^(32 W)`, by `r27` bits of `[y]`,
`[x]` doubled at each, through `[t]` and `[g]`, with `[z]` zero (wide). -/

def productStep (y x a t g z : Nat) : Prog isa := seqs [.block (bitOf sY y), sel t z x sY,
  add a a t z g, shl x, .block [.li .r9 0], half y, .block next]

def product (y x a t g z : Nat) : Prog isa := .loop (productStep y x a t g z) (.nonzero .d .r27)

/-- `a = 2^k x gcd(u, x)`, from the narrow view: `32 w` steps. -/
def aProduct : Prog isa := seqs [.block (countN ++ ctxW), copy wA wZero, product wY wX3 wA wT wNg wZero]

/-! ## The divisions -/

/-- `m` and `r` (wide), with `n` wide (its extra digit zero), and whether `m < n`. -/
def divA : Prog isa := seqs [copy wN wZero, .block ctxw, copy aWN aN, .block ctxW, .block (clrW wN),
  Div.div wA wR wN wDt, sub3 wNg wA wN, .block (stBorrow sLt)]

/-- `m + 1` and `n - r` (narrow), their quotient and remainder, and whether it is zero. -/
def divB : Prog isa := seqs [.block ctxw, copy aOne2 aZero, .block (setOne aOne2), sub3 aNeg1 aZero aOne2,
  sub3 aM1 aM aNeg1, sub3 aD aN aRlo, .block (clrW aM1), Div.div aD aRem aM1 aDt, eqS sExact aRem aZero]

/-! ## `b² - 4 n` -/

/-- `b` (narrow in `aD`, and into the zeroed wide `wU` and `wY`) and `b²` in `wA`. -/
def square : Prog isa := seqs [sub3 aD aD aNeg1, .block ctxW, copy wU wZero, copy wY wZero,
  copy wA wZero, .block ctxw, copy aU aD, copy aY aD, .block (countN ++ ctxW),
  product wY wU wA wT wNg wZero]

/-- `b² - 4 n` in `wR`, and whether `b² < 4 n` and `b² - 4 n < 1`. -/
def minus4n : Prog isa := seqs [shl wN, shl wN, sub3 wR wA wN, .block (stBorrow sC1),
  sub3 wNg wR wOne, .block (stBorrow sC2)]

/-! ## The square root

`16 W` steps, two bits of `[wR]` at a time from its top: the remainder
`[aRm]` takes them, and the root `[aSy]` a bit, one if `4 y + 1` fits in the
remainder (narrow, but for the radicand). -/

def sqrtBody : Prog isa := seqs [.block ctxW, shl wR, .block ctxw, shlC aRm, .block ctxW, shl wR,
  .block ctxw, shlC aRm, copy aTy aSy, shl aTy, .block [.li .r9 1], shlC aTy,
  sub3 aDf aRm aTy, .block (stBorrow sBb), sel aRm aDf aRm sBb,
  .block [.load .w .r9 .r31 sBb, .li .r0 1, .logic .xor .r9 .r9 .r0], shlC aSy, .block next]

def sqrt : Prog isa := seqs [.block ctxw, copy aRm aZero, copy aSy aZero, .block countS,
  .loop sqrtBody (.nonzero .d .r27), eqS sOk5 aRm aZero]

/-! ## The factors -/

/-- The mask: `d e ≥ 2`, `m < n`, the exact division, `b² > 4 n` and the
exact square root. -/
def maskOf : List Instr :=
  [.li .r6 1, .load .w .r0 .r31 sB0, .logic .xor .r0 .r0 .r6, .load .w .r3 .r31 sB1, .logic .xor .r3 .r3 .r6,
    .logic .and .r0 .r0 .r3, .load .w .r3 .r31 sLt, .logic .and .r0 .r0 .r3,
    .load .w .r3 .r31 sExact, .logic .and .r0 .r0 .r3,
    .load .w .r3 .r31 sC1, .logic .xor .r3 .r3 .r6, .logic .and .r0 .r0 .r3,
    .load .w .r3 .r31 sC2, .logic .xor .r3 .r3 .r6, .logic .and .r0 .r0 .r3,
    .load .w .r3 .r31 sOk5, .logic .and .r0 .r0 .r3, .store .w .r0 .r31 Recover.sMask]

/-- `p = (b + ϒ) / 2` into array 5 and `q = (b - ϒ) / 2` into array 6, and the mask. -/
def factors : Prog isa := seqs [add aP aD aSy aZero aNy, .block [.li .r9 0], half aP,
  sub3 aQ aD aSy, .block [.li .r9 0], half aQ, .block maskOf]

/-! ## The function -/

def det : Prog isa := seqs [deMinus, twos, gcd, aProduct, divA, divB, square, minus4n, sqrt, factors]

/-- Once `n` is known valid. -/
def valid : Prog isa := seqs [Recover.loads, Recover.prod, det, Recover.stores]

/-- `vg_rsa_recover_primes_det`. -/
def code : Prog isa :=
  .seq (.block Recover.entry)
    (.seq Recover.nCheck (.seq (.ite (.zero .d .r0) valid Recover.fail) (.block Recover.restore)))

end VG.Impl.Rsa.PPC64LE.RecoverDet
