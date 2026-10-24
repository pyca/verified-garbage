module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.MulMod
public import VerifiedGarbage.Impl.Rsa.PPC64LE.CrtValues
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Precompute
public import VerifiedGarbage.Impl.Bignum.PPC64LE.PublicChecked

/-! # `vg_rsa_recover_primes` on PPC64LE

`vg_rsa_recover_primes(p, p_len, q, q_len, n, n_len, e, e_len, d, d_len,
scratch, scratch_len)`: the first eight arguments in `r3`–`r10`, the others
on the stack. As on ARMv7 (`Impl/Rsa/Arm/Recover.lean`).

The numbers live in the key working space at `scratch`
(`Impl/Rsa/PPC64LE/KeyWs.lean`), with `w = 2 ⌈n_len / 8⌉ + 2` digits of 32
bits: then its stride `4 (w + 2)` is that of Montgomery multiplication's
working space (`Impl/Bignum/Layout.lean`) for numbers of `⌈n_len / 8⌉`
words of 64 bits, whose 8 arrays are the key arrays 20–27. The same working
space read with `W = 2 w + 2` digits has twice the stride, and its array `j`
is the key arrays `2 j` and `2 j + 1`: there the product `M = d e`, which
has up to twice the digits of `n`, and its halvings are computed. The
nonvolatile registers are saved in the key arrays 44 and 45, above those the
function zeroes, as the header's 160 bytes hold its slots.

The pointers, the lengths and the loop counts stay in registers that
Montgomery multiplication leaves alone, so that no address or count is
loaded from memory: `p` in `r21`, `q` in `r23`, `n` in `r24` and `n_len` in
`r25`; `e`, `e_len`, `d` and `d_len` in `r26`, `r27`, `r28` and `r22` until
they are read; then `c = 8 (d_len + e_len)` in `r26`, the candidate in
`r24` and the steps left in `r27`. `n` is checked as `vg_rsa_crt_values`
checks it (it is public); an invalid modulus writes zeros at once.

* `M = d e` by `mulMod` modulo `2^(32 W - 1)`, over the `8 e_len` bits of
  `e`. If `M` is even or 1 (`d e - 1` odd or not positive), no candidate is
  tried and zeros are written: a branch on whether the number of candidates
  tried is 0, which the contract lets leak.
* `m = M - 1` (`M` with its low bit cleared) is halved `c` times, each
  halving and the count `t` of them selected by whether `m` is even:
  `m = 2^t r` with `r` odd.
* Montgomery multiplication's working space is set up for `n`, with `R² mod
  n` (`vg_rsa_public_precompute`'s doublings), and `R mod n` and `n - R mod
  n`, the Montgomery forms of 1 and -1, kept in key arrays.
* For the candidates `g = 2, 3, …`, until one gives the factors or 100 are
  tried (the number of iterations, which the contract lets leak, is the
  only branch on the key): `y = g^r` (in Montgomery form) by `c` steps of
  binary exponentiation from the least significant bit of `r`, each a
  Montgomery product by `g^(2^i)` or 1, chosen under a mask, and a
  Montgomery square of `g^(2^i)`; then `c` squarings of `y` under masks
  that stop at `y² = 1` (found), at `y² = -1` or after `t` of them (not
  found). Each result of Montgomery multiplication has the digits above its
  `2 ⌈n_len / 8⌉` cleared, so that it is a number of the key working space.
* `y` out of Montgomery form, `p = gcd(y - 1, n)` by `inverse`, `q = n /
  p` by the division, the larger first, written under the mask of whether a
  candidate gave them.

Addresses and every other branch depend only on the pointers, the lengths
and `n`.
-/

@[expose] public section

namespace VG.Impl.Rsa.PPC64LE.Recover

open VG.PPC64LE VG.Impl.Rsa.PPC64LE.Keys VG.Impl.Rsa.PPC64LE.Div

/-! ## The header

Bytes 0–39 are the function's slots, 124–132 the shared routines', and 152
the mask of the result (`CrtValues.sMask`, which `CrtValues.mask` reads). -/

def sTc : Nat := 0
def sK : Nat := 4
def sDone : Nat := 8
def sOk : Nat := 12
def sBit : Nat := 16
def sLive : Nat := 20
def sE1 : Nat := 24
def sE2 : Nat := 28
def sLt : Nat := 32
def sMask : Nat := CrtValues.sMask

/-! ## The arrays

With `w` digits: Montgomery multiplication's arrays are 20–27 (its operands
`n` (20), `R² mod n` (21), `y` (24), `g^(2^i)` (25), the multiplicand (26)
and the square (27)); `n`, 1, 0, `R mod n`, `n - R mod n`, and two
temporaries; the division's four. Arrays 0–14 are `inverse`'s, and 44–45
hold the saved registers. -/

def mBase : Nat := 20
def mR2 : Nat := 21
def mY : Nat := 24
def mG : Nat := 25
def mXm : Nat := 26
def mX : Nat := 27
def aN : Nat := 32
def aOne : Nat := 33
def aZ : Nat := 34
def aO : Nat := 35
def aNg : Nat := 36
def aW : Nat := 37
def aU : Nat := 38
def aQ : Nat := 40
def aRm : Nat := 41
def aDv : Nat := 42
def aDt : Nat := 43
/-- The number of arrays zeroed; the saved registers are in the next two. -/
def nArr : Nat := 44

/-- Montgomery indices of the arrays (`mBase + i`). -/
def iR2 : Nat := 1
def iY : Nat := 4
def iG : Nat := 5
def iXm : Nat := 6
def iX : Nat := 7

/-- With `W` digits: zero, `e`, `d`, `M`, the modulus of the product, the
temporaries 5–8 of `mulMod` (and of the halvings), `r` and its copy. -/
def wZ : Nat := 0
def wE : Nat := 1
def wD : Nat := 2
def wM : Nat := 3
def wMod : Nat := 4
def wT : Nat := 5
def wH : Nat := 5
def wU : Nat := 6
def wR : Nat := 14
def wRc : Nat := 15

/-! ## Contexts -/

/-- `W = 2 w + 2` into `r29` and its stride into `r30`. -/
def ctxW : List Instr := [.lsl .r29 .r29 1, .addi .r29 .r29 2] ++ stride

/-- Back to `w = (W - 2) / 2`. -/
def ctxw : List Instr := [.subi .r29 .r29 2, .lsr .d .r29 .r29 1] ++ stride

/-! ## Entry and exit -/

/-- The nonvolatile registers, in the order they are saved. -/
def savedReg (i : Nat) : Reg :=
  [.r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21, .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30,
    .r31].getD i .r14

/-- `w = 2 ⌈n_len / 8⌉ + 2` into `rd`, from `n_len` in `r8`. -/
def wOf (rd : Reg) : List Instr := [.addi rd .r8 7, .lsr .d rd rd 3, .lsl rd rd 1, .addi rd rd 2]

/-- The base of the key array `nArr` into `rd`, the working space's base in
`b` and the stride in `s`. -/
def saveBase (rd b s : Reg) : List Instr := [.li rd nArr, .mul rd rd s, .add rd rd b, .addi rd rd hdr]

/-- The working space's base into `r11` and the nonvolatile registers saved
in its arrays 44–45 (through `r12`). -/
def save : List Instr :=
  CrtValues.stackArg .r11 2 ++ wOf .r12 ++ [.addi .r0 .r12 2, .lsl .r0 .r0 2] ++ saveBase .r12 .r11 .r0 ++
    (List.range 18).map (fun i => .store .d (savedReg i) .r12 (8 * i))

/-- The working space's base, `w` and the stride; `p`, `q`, `n`, `n_len`,
`e`, `e_len` kept, and `d` and `d_len` from the stack. -/
def entry : List Instr :=
  save ++ [.addi .r31 .r11 0] ++ wOf .r29 ++ stride ++
  [.addi .r21 .r3 0, .addi .r23 .r5 0, .addi .r24 .r7 0, .addi .r25 .r8 0, .addi .r26 .r9 0,
    .addi .r27 .r10 0] ++
  CrtValues.stackArg .r28 0 ++ CrtValues.stackArg .r22 1

/-- `n` checked: 0 in `r0` if it is valid. -/
def nCheck : Prog isa := .seq (.block [.addi .r9 .r24 0, .addi .r10 .r25 0]) CrtValues.check

/-- The saved registers restored, through `r11`, `r31` last. -/
def restore : List Instr :=
  saveBase .r11 .r31 .r30 ++ (List.range 18).map (fun i => .load .d (savedReg i) .r11 (8 * i))

/-- Zeros to `p` and `q`, and 0 returned. -/
def fail : Prog isa := seqs [
  .block [.addi .r5 .r21 0, .addi .r8 .r25 0], CrtValues.zeroBytes,
  .block [.addi .r5 .r23 0, .addi .r8 .r25 0], CrtValues.zeroBytes,
  .block [.li .r3 0]]

/-! ## The numbers -/

/-- Every array zeroed. -/
def zeroAll : Prog isa := .seq (.block [.li .r8 nArr, .mul .r8 .r8 .r30, .lsr .d .r8 .r8 2]) (zeroArrays .r8)

/-- `[j] :=` the `rL` bytes at `rP`. -/
def loadR (rP rL : Reg) (j : Nat) : List (Prog isa) :=
  [.block [.addi .r6 rP 0, .addi .r8 rL 0], CrtValues.load j]

/-- `n` read, then with `W` `e` and `d` (to the arrays `wE` and `wD`), and
`c = 8 (e_len + d_len)` into `r26`. -/
def loads : Prog isa :=
  seqs ([zeroAll] ++ loadR .r24 .r25 aN ++ [.block ctxW] ++ loadR .r26 .r27 wE ++ loadR .r28 .r22 wD ++
    [.block [.add .r26 .r27 .r22, .lsl .r26 .r26 3]])

/-- The top digit of `[j]` := `2^31`: `[j] = 2^(32 w - 1)` if it was zero. -/
def setTop (j : Nat) : List Instr :=
  ptr .r5 j ++ [.lsl .r0 .r29 2, .add .r5 .r5 .r0, .subi .r5 .r5 4, .li .r0 1, .lsl .r0 .r0 31,
    .store .w .r0 .r5 0]

/-- With `W`: the modulus `2^(32 W - 1)`, and `8 e_len` steps. -/
def prodSet : List Instr := setTop wMod ++ [.lsl .r4 .r27 3]

/-- `M := d e`. -/
def prod : Prog isa := .seq (.block prodSet) (mulMod wZ wE wD wM wMod wT)

/-- The low bit of `M` into `sBit`, and `M`'s cleared. -/
def skipBits : List Instr := bitOf sBit wM ++ clrLow wM

/-- `r0 := 0` iff `M` was odd and `m = M - 1` is not zero (`0 - m`
borrows), and back to `w`. -/
def skipTest : List Instr :=
  [.load .w .r0 .r31 sBit, .logic .and .r0 .r0 .r9, .li .r3 1, .logic .xor .r0 .r0 .r3] ++ ctxw

/-- `M = d e`, and whether to try candidates. -/
def numbers : Prog isa := seqs [loads, prod, .block skipBits, sub3 wT wZ wM, .block skipTest]

/-! ## `m = 2^t r` -/

/-- `r := m`, `t := 0`, and the count. -/
def halfInit : Prog isa := seqs [copy wR wM, .block [.li .r0 0, .store .w .r0 .r31 sTc, .addi .r27 .r26 0]]

/-- The bit of `m` even into `sBit`, and `t +=` it. -/
def halfBit : List Instr :=
  bitOf sBit wR ++ [.load .w .r0 .r31 sBit, .li .r3 1, .logic .xor .r0 .r0 .r3, .store .w .r0 .r31 sBit,
    .load .w .r3 .r31 sTc, .add .r3 .r3 .r0, .store .w .r3 .r31 sTc]

/-- A halving: `m := m / 2` and `t += 1` if `m` is even. -/
def halfBody : Prog isa := seqs [copy wU wR, copy wH wR, .block [.li .r9 0], half wH, .block halfBit,
  sel wR wU wH sBit, .block [.subi .r27 .r27 1]]

/-- With `W`, back to `w` after. -/
def halving : Prog isa := seqs [.block ctxW, halfInit, .loop halfBody (.nonzero .d .r27), .block ctxw]

/-! ## Montgomery multiplication's working space -/

/-- Montgomery multiplication's context: its array 0 into `r10`, `2 ⌈n_len /
8⌉ = w - 2` into `r11` and its arrays' size into `r29`. -/
def mpre : List Instr := ptr .r10 mBase ++ [.subi .r11 .r29 2, .addi .r29 .r30 0]

/-- Back to `w`. -/
def mpost : List Instr := [.addi .r29 .r11 2]

/-- The digits above the low `w - 2` of `[j]` cleared. -/
def clrTop (j : Nat) : List Instr :=
  ptr .r5 j ++ [.lsl .r0 .r29 2, .add .r5 .r5 .r0, .subi .r5 .r5 8, .li .r0 0, .store .w .r0 .r5 0,
    .store .w .r0 .r5 4]

/-- A Montgomery product `[o] := [a] [b] R⁻¹ mod n` (Montgomery indices),
then `[o]`'s top digits cleared. -/
def mmul (o a b : Nat) : List (Prog isa) :=
  [.block mpre, VG.Impl.Bignum.PPC64LE.PublicChecked.montOp o a b, .block (mpost ++ clrTop (mBase + o))]

/-- `R² mod n` into Montgomery array 1: its base into `r5`, the
accumulator's and the temporary's into `r8` and `r9`. -/
def r2Set : List Instr := [.add .r5 .r10 .r29, .add .r8 .r5 .r29, .add .r9 .r8 .r29]

/-- 1, `n` in Montgomery array 0 and `-n⁻¹ mod 2³²` into `r12`; `R² mod n`
with its top digits cleared; `R mod n` (from `1 · R²`) and `n - R mod n`. -/
def mont : Prog isa := seqs ([.block (setOne aOne), copy mBase aN,
  .block (mpre ++ VG.Impl.Bignum.PPC64LE.PublicChecked.minv ++ r2Set), VG.Impl.Bignum.PPC64LE.Precompute.r2, .block (mpost ++ clrTop mR2),
  copy mXm aOne] ++ mmul iXm iXm iR2 ++ [copy aO mXm, sub3 aNg aN aO])

/-! ## A candidate -/

/-- `g = r24 + 2` into `[mG]`, `y := 1` (in Montgomery form), `r`'s copy
and the count of its bits. -/
def candSet : Prog isa := seqs [copy mG aZ,
  .block (ptr .r5 mG ++ [.addi .r0 .r24 2, .store .w .r0 .r5 0]),
  copy mY aO, .block ctxW, copy wRc wR, .block (ctxw ++ [.addi .r27 .r26 0])]

/-- A bit of `r`: the multiplicand `g^(2^i)` or 1, by the bit of `r`'s copy
shifted out; `y` times it, and `g^(2^i)` squared. -/
def expBody : Prog isa := seqs ([.block (ctxW ++ bitOf sBit wRc ++ [.li .r9 0]), half wRc,
  .block ctxw, sel mXm aO mG sBit] ++ mmul iY iY iXm ++ mmul iG iG iG ++ [.block [.subi .r27 .r27 1]])

/-- `y` to the power `r`. -/
def expLoop : Prog isa := .loop expBody (.nonzero .d .r27)

/-- `done := (y = 1) ∨ (y = -1)`, `ok := 0`, `k := 0`, and the count. -/
def sqInit : List Instr :=
  [.load .w .r0 .r31 sE1, .load .w .r3 .r31 sE2, .logic .or .r0 .r0 .r3, .store .w .r0 .r31 sDone,
    .li .r0 0, .store .w .r0 .r31 sOk, .store .w .r0 .r31 sK, .addi .r27 .r26 0]

/-- After `x = y²`, with `x = 1` in `sE1` and `x = -1` in `sE2`: the
squaring is live if not done and `k < t`; it finds `y` if `x = 1`, stops if
`x = -1` or `k + 1 = t`, and otherwise `y := x` (`sLive`). -/
def sqMasks : List Instr :=
  [.load .w .r3 .r31 sK, .load .w .r4 .r31 sTc, .sub .r5 .r3 .r4, .lsr .d .r5 .r5 63,
    .load .w .r6 .r31 sDone, .li .r0 1, .logic .xor .r7 .r6 .r0, .logic .and .r5 .r5 .r7,
    .addi .r3 .r3 1, .logic .xor .r3 .r3 .r4, .subi .r3 .r3 1, .lsr .d .r3 .r3 63,
    .load .w .r4 .r31 sE2, .logic .or .r3 .r3 .r4,
    .load .w .r4 .r31 sE1, .load .w .r7 .r31 sOk, .logic .and .r8 .r5 .r4, .logic .or .r7 .r7 .r8,
    .store .w .r7 .r31 sOk,
    .logic .or .r8 .r4 .r3, .logic .and .r8 .r8 .r5, .logic .or .r6 .r6 .r8, .store .w .r6 .r31 sDone,
    .logic .xor .r8 .r8 .r0, .logic .and .r8 .r8 .r5, .store .w .r8 .r31 sLive]

/-- `k += 1`, and the count. -/
def sqNext : List Instr :=
  [.load .w .r3 .r31 sK, .addi .r3 .r3 1, .store .w .r3 .r31 sK, .subi .r27 .r27 1]

/-- A squaring under the masks. -/
def sqBody : Prog isa := seqs (mmul iX iY iY ++ [eqS sE1 mX aO, eqS sE2 mX aNg, .block sqMasks,
  copy aU mY, sel mY aU mX sLive, .block sqNext])

def sqLoop : Prog isa := .loop sqBody (.nonzero .d .r27)

/-- The candidates tried `+= 1`, and `r0` nonzero to go on: fewer than 100
tried and not `ok`. -/
def candNext : List Instr :=
  [.addi .r24 .r24 1, .subi .r0 .r24 100, .lsr .d .r0 .r0 63, .load .w .r3 .r31 sOk, .li .r4 1,
    .logic .xor .r3 .r3 .r4, .logic .and .r0 .r0 .r3]

/-- A candidate. -/
def candBody : Prog isa := seqs ([candSet] ++ mmul iG iG iR2 ++ [expLoop, eqS sE1 mY aO, eqS sE2 mY aNg,
  .block sqInit, sqLoop, .block candNext])

/-- The candidates, from `r24 = 0`. -/
def candLoop : Prog isa := .seq (.block [.li .r24 0]) (.loop candBody (.nonzero .d .r0))

/-! ## The factors -/

/-- `ok` into the mask, and `y` out of Montgomery form. -/
def finY : Prog isa := seqs ([.block [.load .w .r0 .r31 sOk, .store .w .r0 .r31 sMask], copy mXm aOne] ++
  mmul iY iY iXm)

/-- `inverse`'s start: `(u, v, x₁, x₂) = (y - 1, n, 1, 0)`, its modulus `n`,
zero and the negated modulus. -/
def gcdSet : Prog isa := seqs [sub3 0 mY aOne, copy 1 aN, copy aM aN, copy 2 aZ, .block (setOne 2),
  copy 3 aZ, copy aZero aZ, sub3 aNM aZero aM]

/-- The digit above the `w` of `[j]` cleared, as the division's divisor needs. -/
def clrW (j : Nat) : List Instr := ptr .r5 j ++ [.lsl .r0 .r29 2, .add .r5 .r5 .r0, .li .r0 0, .store .w .r0 .r5 0]

/-- `n` divided by `p`. -/
def divide : Prog isa := seqs [copy aQ aN, copy aDv 1, .block (clrW aDv), div aQ aRm aDv aDt]

/-- `p < q` into `sLt`, and the larger into 5, the smaller into 6. -/
def order : Prog isa := seqs [sub3 aW 1 aQ, .block (stBorrow sLt), sel 5 1 aQ sLt, sel 6 aQ 1 sLt]

/-- The factors written out under the mask, and the mask returned. -/
def stores : Prog isa := seqs [
  .block ([.addi .r5 .r21 0, .addi .r8 .r25 0] ++ CrtValues.mask), CrtValues.storeBytes 5,
  .block ([.addi .r5 .r23 0, .addi .r8 .r25 0] ++ CrtValues.mask), CrtValues.storeBytes 6,
  .block [.load .w .r3 .r31 sMask]]

def fin : Prog isa := seqs [finY, gcdSet, inverse, divide, order, stores]

/-- Once `M` is known odd and above 1. -/
def rest : Prog isa := seqs [halving, mont, candLoop, fin]

/-- Once `n` is known valid. -/
def valid : Prog isa := .seq numbers (.ite (.zero .d .r0) rest fail)

/-- `vg_rsa_recover_primes`. -/
def code : Prog isa :=
  .seq (.block entry) (.seq nCheck (.seq (.ite (.zero .d .r0) valid fail) (.block restore)))

end VG.Impl.Rsa.PPC64LE.Recover
