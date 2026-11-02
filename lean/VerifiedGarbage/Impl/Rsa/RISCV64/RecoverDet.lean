module

public import VerifiedGarbage.Impl.Rsa.RISCV64.MulMod
public import VerifiedGarbage.Impl.Rsa.RISCV64.Div
public import VerifiedGarbage.Impl.Bignum.RISCV64.Precompute

/-!
# `vg_rsa_recover_primes_det` on RISC-V

`vg_rsa_recover_primes_det(p = a0, p_len = a1, q = a2, q_len = a3, n = a4,
n_len = a5, e = a6, e_len = a7, d, d_len, scratch, scratch_len)`, the last
four on the stack. SP 800-56B Rev. 2 Appendix C.2 without a branch on a
secret, as on PPC64LE (`Impl/Rsa/PPC64LE/RecoverDet.lean`), in words of 64
bits and computing what `Proof/Rsa/RecoverDetModel.lean` models, with `nb =
64 w` narrow and `wb = 64 W` wide bits.

The numbers live in the key working space (`Impl/Rsa/RISCV64/KeyWs.lean`)
with `w = ⌈n_len / 8⌉ + 1` words (narrow), a word more than `n` needs, so
that `d e` fits; read with `W = 2 w + 2` words (wide), the same working
space has twice the stride, and its array `j` is the narrow arrays `2 j` and
`2 j + 1`. A narrow number copied into the low half of a wide array of zeros
is that wide number.

* `n` is checked as `vg_rsa_public_precompute` checks it (`Precompute.check`),
  the only branch on data; an invalid modulus writes zeros at once.
* `d e` by `mulMod` modulo `2^(64 W - 1)` over the `8 e_len` bits of `e`
  (wide), `x = d e - 1` and whether `d e ≥ 2`;
* `64 w` steps that halve `u = n - 1` while it is even, and while `x` is
  even too halve it and double `2^k x` (`u` and `x` narrow, `2^k x` wide);
* `gcd(u, x)` by the binary GCD (`gcdStep`: `Proof/Rsa/KeyMath.lean`'s
  `invStep` without the cofactors), `u` odd, in `32 w + 4 n_len`
  iterations of two steps;
* `a = gcd(u, x) · 2^k x` modulo `2^(64 W)` by a schoolbook product of words
  (`mulLow`, `mul` and `mulhu`), `m = ⌊a / n⌋`, `r = a mod n` (`Div.div`,
  wide), and whether `m < n`;
* `b - 1 = (n - r) / (m + 1)` (`Div.div`, narrow), `b² - 4 n` (`mulLow`) and
  whether `b² > 4 n`;
* its square root, two bits at a time from the top in `32 W` steps
  (`sqrtBody`): the wide radicand shifted left into the narrow remainder,
  which keeps `4 y + 1` where it fits;
* `p = (b + ϒ) / 2` and `q = (b - ϒ) / 2`, written under the mask of every
  check, which is returned.

Registers kept throughout: `s1` `n`, `s2` `n_len`, `s3` `p`, `s4` `q`, `s5`
`e`, `s6` `e_len`, `a0` `d`, `a1` `d_len`; `s9`–`s11` the working space's
(`w` or `W`, the stride, the base), `s7` the count of each loop, and `s8`
and `a2`, `a3`, `a6` the product's. Every address is computed from the base,
the stride and `s9`, and every count from `s9` and `n_len`: the addresses and
branches depend only on them and on `n`.
-/

@[expose] public section

namespace VG.Impl.Rsa.RISCV64.RecoverDet

open VG.RISCV64 VG.Impl.Bignum.RISCV64 VG.Impl.Rsa.RISCV64.Keys VG.Impl.Rsa.RISCV64.Div

/-! ## The header

Bytes 0–95 hold the caller's `s0`–`s11`, 128–144 the shared routines'
slots, and from 152 this function's. -/

/-- `d e < 1` and `d e - 1 < 1`. -/
def sB0 : Nat := 152
def sB1 : Nat := 160
/-- A step of the halvings: the low bits of `u` and `x`, `u` even, and both even. -/
def sU : Nat := 168
def sX : Nat := 176
def sEven : Nat := 184
def sBoth : Nat := 192
/-- `m < n`. -/
def sLt : Nat := 200
/-- `(n - r) mod (m + 1) = 0`. -/
def sExact : Nat := 208
/-- `b² < 4 n` and `b² - 4 n < 1`. -/
def sC1 : Nat := 216
def sC2 : Nat := 224
/-- The square root's borrow. -/
def sBb : Nat := 232
/-- The square root's remainder is zero. -/
def sOk5 : Nat := 240
/-- The mask of every check. -/
def sMask : Nat := 248

/-! ## The arrays

Wide (`W` words; the wide array `j` is the narrow arrays `2 j` and `2 j + 1`):
zero, `e`, `d`, `d e`, the modulus `2^(64 W - 1)`, `mulMod`'s temporaries
5–8, `x`, one, `2^k x`, `a` (then `m`), the remainder `r` (then `b² - 4 n`),
`n` (then `4 n`), the division's temporary, a temporary, the GCD, `b`, `b²`. -/

def wZ : Nat := 0
def wE : Nat := 1
def wD : Nat := 2
def wM : Nat := 3
def wMod : Nat := 4
def wT : Nat := 5
def wX : Nat := 9
def wOne : Nat := 10
def wX3 : Nat := 11
def wA : Nat := 12
def wR : Nat := 13
def wN : Nat := 14
def wDt : Nat := 15
def wT2 : Nat := 16
def wG : Nat := 17
def wB : Nat := 18
def wSq : Nat := 19

/-- Narrow (`w` words), from 40 on, past the wide arrays 0–19: `n`, one,
zero, `u`, `x` halved, a temporary; the GCD's `u`, `v` and temporaries; the
second division's `-1`, `m + 1`, `n - r` (then `b - 1` and `b`), remainder
and temporary; the square root's remainder, root, `4 y + 1` and difference;
the factors and the temporary of their sum. -/
def aN : Nat := 40
def aOne : Nat := 41
def aZero : Nat := 42
def aU : Nat := 43
def aX2 : Nat := 44
def aT : Nat := 45
def gU : Nat := 46
def gV : Nat := 47
def gT1 : Nat := 48
def gT2 : Nat := 49
def gT3 : Nat := 50
def aNeg1 : Nat := 51
def aM1 : Nat := 52
def aD : Nat := 53
def aRem : Nat := 54
def aDt : Nat := 55
def aRm : Nat := 56
def aSy : Nat := 57
def aTy : Nat := 58
def aDf : Nat := 59
def aP : Nat := 60
def aQ : Nat := 61
def aNy : Nat := 62

/-- The number of narrow arrays, all zeroed. -/
def nArr : Nat := 63

/-! ## Contexts -/

/-- The narrow `w = ⌈n_len / 8⌉ + 1` into `s9` and its stride `8 (w + 2)` into `s10`. -/
def ctxInit : List Instr :=
  [.addi .s9 .s2 7, .shift .srl .d .s9 .s9 3, .addi .s9 .s9 1, .addi .s10 .s9 2,
    .shift .sll .d .s10 .s10 3]

/-- `W = 2 w + 2` into `s9` and its stride `8 (W + 2)`, twice the narrow one. -/
def ctxW : List Instr :=
  [.shift .sll .d .s9 .s9 1, .addi .s9 .s9 2, .shift .sll .d .s10 .s10 1]

/-- Back to `w = (W - 2) / 2`. -/
def ctxw : List Instr :=
  [.addi .s9 .s9 (-2), .shift .srl .d .s9 .s9 1, .shift .srl .d .s10 .s10 1]

/-! ## Entry and exit -/

/-- The working space (the stack argument 2) and the registers saved there,
then the pointers and lengths into the registers kept. -/
def entry : List Instr :=
  save 16 ++
  [mov .s3 .a0, mov .s4 .a2, mov .s1 .a4, mov .s2 .a5, mov .s5 .a6, mov .s6 .a7, .addSp .t0 0,
    .load .d .a0 .t0 0, .load .d .a1 .t0 8]

/-- Whether `n` is a valid modulus, in `s0`: 0 if it is. -/
def nCheck : Prog isa := .seq (.block [mov .s7 .s1, mov .s8 .s2]) Precompute.check

/-- Zeros to `p` and `q`, and 0 returned. -/
def fail : Prog isa := seqs [zeroBytes .s3 .s2, zeroBytes .s4 .s2, .block [.li .a0 0]]

/-! ## Operations -/

/-- `[j] := 2 [j] + t4` modulo `2^(64 s9)`, for `t4` 0 or 1, the bit shifted
out in `t4`. -/
def shlC (j : Nat) : Prog isa := .seq (.block (ptr .t0 j ++ [mov .t3 .s9])) (countLoop .t3 shlBody)

/-- `[j] := 2 [j]` modulo `2^(64 s9)`, the bit shifted out in `t4`. -/
def shl (j : Nat) : Prog isa := .seq (.block [.li .t4 0]) (shlC j)

/-- `[o] := [a] + [b]` modulo `2^(64 s9)`, through `[t] = [z] - [b]`, with
`[z]` zero. -/
def add (o a b z t : Nat) : Prog isa := .seq (sub3 t z b) (sub3 o a t)

/-- One word of a row of the product: `t4 + [t0] + a6 [t1]`, its low word to
`[t0]` and its high word, the carry, into `t4`. -/
def mulBody : List Instr :=
  [.load .d .t5 .t1 0, .mul .t6 .a6 .t5, .mulhu .t5 .a6 .t5, .load .d .a4 .t0 0,
    .add .t6 .t6 .a4, .sltu .a4 .t6 .a4, .add .t5 .t5 .a4,
    .add .t6 .t6 .t4, .sltu .a4 .t6 .t4, .add .t5 .t5 .a4,
    .store .d .t6 .t0 0, mov .t4 .t5, .addi .t0 .t0 8, .addi .t1 .t1 8]

/-- A row: `[o] += y_i [x] 2^(64 i)` modulo `2^(64 s9)`, for `y_i` the word
at `a2`, `a3` the word `i` of `[o]` and `s8 = s9 - i` words to go; then the
next row's. -/
def mulRow (x : Nat) : Prog isa :=
  .seq (.block ([.load .d .a6 .a2 0, mov .t0 .a3] ++ ptr .t1 x ++ [mov .t3 .s8, .li .t4 0]))
    (.seq (countLoop .t3 mulBody) (.block [.addi .a2 .a2 8, .addi .a3 .a3 8, .addi .s8 .s8 (-1)]))

/-- `[o] := [y] [x]` modulo `2^(64 s9)`, from `[o] = 0`: a row for each of
the `s9` words of `[y]`. -/
def mulLow (o y x : Nat) : Prog isa :=
  .seq (.block (ptr .a2 y ++ ptr .a3 o ++ [mov .s8 .s9])) (.loop (mulRow x) (.nonzero .s8))

/-- A step less. -/
def next : List Instr := [.addi .s7 .s7 (-1)]

/-! ## `d e - 1` (wide) -/

/-- `n` (narrow), then with `W` `e` and `d`, and the modulus `2^(64 W - 1)`:
its top word `2^63`. -/
def loads : Prog isa := seqs [load aN .s1 .s2, .block ctxW, load wE .s5 .s6, load wD .a0 .a1,
  .block (ptr .t0 wMod ++ [.shift .sll .d .t5 .s9 3, .add .t0 .t0 .t5, .addi .t0 .t0 (-8),
    .li .t5 1, .shift .sll .d .t5 .t5 63, .store .d .t5 .t0 0])]

/-- `d e` by `8 e_len` steps of `mulMod` modulo `2^(64 W - 1)`. -/
def prod : Prog isa := .seq (.block [.shift .sll .d .s7 .s6 3]) (mulMod wZ wE wD wM wMod wT)

/-- One (`wOne`), `x = d e - 1`, and the borrows of `d e - 1` and `x - 1`. -/
def deMinus : Prog isa := seqs [.block (setOne wOne), sub3 wX wM wOne, .block (stBorrow sB0),
  sub3 wT2 wX wOne, .block (stBorrow sB1)]

/-! ## The halvings -/

/-- `2^k x := x` (wide); `u = n - 1` and `x` (narrow); `64 w` steps. -/
def twosInit : Prog isa := seqs [copy wX3 wX, .block ctxw, .block (setOne aOne), sub3 aU aN aOne,
  copy aX2 (2 * wX), .block [.shift .sll .d .s7 .s9 6]]

/-- The flags of a step: `even := ¬u₀` and `both := ¬u₀ ∧ ¬x₀`. -/
def twosFlags : List Instr :=
  bitOf sU aU ++ bitOf sX aX2 ++
  [.load .d .t5 .s11 sU, .load .d .t6 .s11 sX, .logicImm .xor .t5 .t5 1, .logicImm .xor .t6 .t6 1,
    .store .d .t5 .s11 sEven, .logic .and .t6 .t6 .t5, .store .d .t6 .s11 sBoth]

/-- `[j]` halved if the slot `sl` holds 1, through `aT`. -/
def halfIf (j sl : Nat) : Prog isa := seqs [copy aT j, .block [.li .t4 0], half aT, sel j j aT sl]

/-- A step: `u` halved if even, `x` halved and `2^k x` doubled (wide) if both are. -/
def twosBody : Prog isa := seqs [.block twosFlags, halfIf aU sEven, halfIf aX2 sBoth, .block ctxW,
  copy wT2 wX3, shl wT2, sel wX3 wX3 wT2 sBoth, .block (ctxw ++ next)]

def twos : Prog isa := seqs [twosInit, .loop twosBody (.nonzero .s7)]

/-! ## The GCD (narrow) -/

/-- A step of the binary GCD on `(u, v) = ([gU], [gV])`, `v` odd: with `odd`
the low bit of `u` and `c = odd ∧ u < v`, `v := c ? u : v` and `u := (odd ?
(c ? v - u : u - v) : u) / 2`. -/
def gcdStep : Prog isa := seqs [
  .block (bitOf sOdd gU), sub3 gT1 gU gV, .block (stBorrow sB ++ andS sC sOdd sB),
  sub3 gT2 gV gU, sel gV gV gU sC, sel gT3 gT1 gT2 sC, sel gU gU gT3 sOdd,
  .block [.li .t4 0], half gU]

/-- `gcd(x, u)` into `[gV]`, from `(x, u)`: `32 w + 4 n_len` iterations of
two steps, `x u < 2^(64 w + 8 n_len)`; then into the low half of the wide
`wG`. -/
def gcd : Prog isa := seqs [copy gU aX2, copy gV aU,
  .block [.shift .sll .d .s7 .s9 5, .shift .sll .d .t5 .s2 2, .add .s7 .s7 .t5],
  .loop (seqs [gcdStep, gcdStep, .block next]) (.nonzero .s7), copy (2 * wG) gV]

/-! ## `a`, `m` and `r` (wide) -/

/-- `a = gcd(u, x) · 2^k x` modulo `2^(64 W)`; `n` into the zeroed wide
`wN`, `m = ⌊a / n⌋` and `r = a mod n`, and whether `m < n`. -/
def divA : Prog isa := seqs [copy (2 * wN) aN, .block ctxW, mulLow wA wG wX3,
  div wA wR wN wDt, sub3 wT2 wA wN, .block (stBorrow sLt)]

/-! ## `b` (narrow) -/

/-- `-1`, `m + 1` and `n - r` (narrow), their quotient and remainder, and
whether it is zero. -/
def divB : Prog isa := seqs [.block ctxw, sub3 aNeg1 aZero aOne, sub3 aM1 (2 * wA) aNeg1,
  sub3 aD aN (2 * wR), div aD aRem aM1 aDt, eqS sExact aRem aZero]

/-! ## `b² - 4 n` (wide) -/

/-- `b` (narrow in `aD`, and into the zeroed wide `wB`), `b²` and `4 n`, `b² - 4 n` in `wR`, and
whether `b² < 4 n` and `b² - 4 n < 1`. -/
def minus4n : Prog isa := seqs [sub3 aD aD aNeg1, copy (2 * wB) aD, .block ctxW, mulLow wSq wB wB,
  shl wN, shl wN, sub3 wR wSq wN, .block (stBorrow sC1), sub3 wT2 wR wOne, .block (stBorrow sC2)]

/-! ## The square root

`32 W` steps, two bits of `[wR]` at a time from its top: the remainder
`[aRm]` takes them, and the root `[aSy]` a bit, one if `4 y + 1` fits in the
remainder (narrow, but for the radicand). -/

def sqrtBody : Prog isa := seqs [.block ctxW, shl wR, .block ctxw, shlC aRm, .block ctxW, shl wR,
  .block ctxw, shlC aRm, copy aTy aSy, shl aTy, .block [.li .t4 1], shlC aTy,
  sub3 aDf aRm aTy, .block (stBorrow sBb), sel aRm aDf aRm sBb,
  .block [.load .d .t5 .s11 sBb, .logicImm .xor .t4 .t5 1], shlC aSy, .block next]

def sqrt : Prog isa := seqs [.block ctxw,
  .block [.shift .sll .d .s7 .s9 6, .addi .s7 .s7 64],
  .loop sqrtBody (.nonzero .s7), eqS sOk5 aRm aZero]

/-! ## The factors -/

/-- The mask: `d e ≥ 2`, `m < n`, the exact division, `b² > 4 n` and the
exact square root. -/
def maskOf : List Instr :=
  [.load .d .t5 .s11 sB0, .logicImm .xor .t5 .t5 1, .load .d .t6 .s11 sB1, .logicImm .xor .t6 .t6 1,
    .logic .and .t5 .t5 .t6, .load .d .t6 .s11 sLt, .logic .and .t5 .t5 .t6,
    .load .d .t6 .s11 sExact, .logic .and .t5 .t5 .t6,
    .load .d .t6 .s11 sC1, .logicImm .xor .t6 .t6 1, .logic .and .t5 .t5 .t6,
    .load .d .t6 .s11 sC2, .logicImm .xor .t6 .t6 1, .logic .and .t5 .t5 .t6,
    .load .d .t6 .s11 sOk5, .logic .and .t5 .t5 .t6, .store .d .t5 .s11 sMask]

/-- `p = (b + ϒ) / 2` and `q = (b - ϒ) / 2`, and the mask. -/
def factors : Prog isa := seqs [add aP aD aSy aZero aNy, .block [.li .t4 0], half aP,
  sub3 aQ aD aSy, .block [.li .t4 0], half aQ, .block maskOf]

/-- The mask `0 - [sMask]` into `t4`. -/
def mask : List Instr := [.load .d .t4 .s11 sMask, .li .t5 0, .sub .t4 .t5 .t4]

/-- The factors written out under the mask, and the mask returned. -/
def stores : Prog isa := seqs [.block mask, storeBytes aP .s3 .s2, storeBytes aQ .s4 .s2,
  .block [.load .d .a0 .s11 sMask]]

/-! ## The function -/

/-- `w`, the stride and every array zeroed. -/
def setup : Prog isa := .seq (.block ctxInit) (zeroArrays nArr)

def det : Prog isa := seqs [deMinus, twos, gcd, divA, divB, minus4n, sqrt, factors]

/-- Once `n` is known valid. -/
def valid : Prog isa := seqs [setup, loads, prod, det, stores]

/-- `vg_rsa_recover_primes_det`. -/
def code : Prog isa :=
  .seq (.block entry) (.seq nCheck (.seq (.ite (.zero .s0) valid fail) (.block restore)))

end VG.Impl.Rsa.RISCV64.RecoverDet
