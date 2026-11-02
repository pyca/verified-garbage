module

public import VerifiedGarbage.Impl.Rsa.Arm.MulMod
public import VerifiedGarbage.Impl.Rsa.Arm.CrtValues
public import VerifiedGarbage.Impl.Bignum.Arm.PcFn
public import VerifiedGarbage.Impl.Bignum.Arm.MontSelected

/-! # `vg_rsa_recover_primes` on ARMv7

`vg_rsa_recover_primes(p, p_len, q, q_len, n, n_len, e, e_len, d, d_len,
scratch, scratch_len)`: the first four arguments in `r0`–`r3`, the others
on the stack. The function pushes a frame of 56 bytes, as
`vg_rsa_public_checked` does (word 0 then holds the base of the Montgomery
working space, word 1 `p`, word 2 `q`). `n` is checked as
`vg_rsa_public_checked` checks it (it is public); an invalid modulus writes
zeros at once.

The numbers live in the key working space at `scratch`
(`Impl/Rsa/Arm/KeyWs.lean`), with `w = 2 ⌈n_len / 8⌉ + 2` words of 32 bits:
then its stride is that of Montgomery multiplication's working space
(`Proof/Rsa/MontContract.lean`) for numbers of `⌈n_len / 8⌉` words of 64 bits, which
is placed so that its 8 arrays are the key arrays 20–27, and its header
lies in the arrays 16–19. The same working space read with `W = 2 w + 2`
words has twice the stride, and its array `j` is the key arrays `2 j` and
`2 j + 1`: there the product `M = d e`, which has up to twice the words of
`n`, and its halvings are computed.

* `M = d e` by `mulMod` modulo `2^(32 W - 1)`, over the `8 e_len` bits of
  `e`. If `M` is even or 1 (`d e - 1` odd or not positive), no candidate is
  tried and zeros are written: a branch on whether the number of candidates
  tried is 0, which the contract lets leak.
* `m = M - 1` (`M` with its low bit cleared) is halved `c = 8 (d_len +
  e_len)` times, each halving and the count `t` of them selected by whether
  `m` is even: `m = 2^t r` with `r` odd.
* Montgomery multiplication's working space is set up for `n`, with `R² mod
  n` (`vg_rsa_public_precompute`'s computation), and `R mod n` and `n - R
  mod n`, the Montgomery forms of 1 and -1, kept in key arrays.
* For the candidates `g = 2, 3, …`, until one gives the factors or 100 are
  tried (the number of iterations, which the contract lets leak, is the
  only branch on the key): `y = g^r` (in Montgomery form) by `c` steps of
  binary exponentiation from the least significant bit of `r`, each a
  Montgomery product by `g^(2^i)` or 1, chosen under a mask, and a
  Montgomery square of `g^(2^i)`; then `c` squarings of `y` under masks
  that stop at `y² = 1` (found), at `y² = -1` or after `t` of them (not
  found). Each result of Montgomery multiplication has the words above its
  `⌈n_len / 8⌉` of 64 bits cleared, so that it is a number of the key
  working space.
* `y` out of Montgomery form, `p = gcd(y - 1, n)` by `inverse`, `q = n /
  p` by the division, the larger first, written under the mask of whether a
  candidate gave them.

Addresses and every other branch depend only on the pointers, the lengths
and `n`.
-/

@[expose] public section

namespace VG.Impl.Rsa.Arm.Recover
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Rsa.Arm.Keys

/-! ## The frame

After the push of `r0`–`r12` and `lr`, the stack arguments start at byte
56: `n`, `n_len`, `e`, `e_len`, `d`, `d_len`, `scratch`, `scratch_len`. -/

def oP : Nat := 4
def oQ : Nat := 8
def aoN : Nat := 56
def aoK : Nat := 60
def aoE : Nat := 64
def aoEl : Nat := 68
def aoD : Nat := 72
def aoDl : Nat := 76
def aoS : Nat := 80

/-! ## The header

Bytes 0–19 are the division's (16: `w`), 100–112 the shared routines', and
132 the mask of the result (`CrtValues.sMask`, which `CrtValues.store`
reads). -/

def sTc : Nat := 20
def sCand : Nat := 24
def sK : Nat := 28
def sDone : Nat := 32
def sOk : Nat := 36
def sBit : Nat := 40
def sLive : Nat := 44
def sE1 : Nat := 48
def sE2 : Nat := 52
def sCnt : Nat := 56
def sLt : Nat := 60
def sMask : Nat := 132

/-! ## The arrays

With `w` words: Montgomery multiplication's arrays are 20–27 (its operands
`n` (20), `y` (21), `R² mod n` (24), `g^(2^i)` (25), the multiplicand (26)
and the square (27)); `n`, 1, 0, `R mod n`, `n - R mod n`, and two
temporaries; the division's four. Arrays 0–14 are `inverse`'s. -/

def mBase : Nat := 20
def mY : Nat := 21
def mR2 : Nat := 24
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
/-- The number of arrays. -/
def nArr : Nat := 44

/-- Montgomery indices of the arrays (`mBase + i`). -/
def iY : Nat := 1
def iR2 : Nat := 4
def iG : Nat := 5
def iXm : Nat := 6
def iX : Nat := 7

/-- With `W` words: zero, `e`, `d`, `M`, the modulus of the product, the
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

/-- The base of the working space into `r8`. -/
def ctxB : List Instr := [.ldrSp .r8 aoS]

/-- `w` into `r9` and its stride into `r7`. -/
def ctxw : List Instr := [.ldr .r9 .r8 16] ++ stride

/-- `W = 2 w + 2` into `r9` and its stride into `r7`. -/
def ctxW : List Instr := [.ldr .r9 .r8 16, .mov .r9 (.shifted .r9 .lsl 1), .dp .add .r9 .r9 (.imm 2)] ++ stride

/-- After Montgomery multiplication: the working space with `w`. -/
def ctx : List Instr := ctxB ++ ctxw

/-- The base of Montgomery multiplication's working space into `r0`. -/
def mont0 : List Instr := [.ldrSp .r0 0]

/-! ## Entry and exits -/

/-- `p` saved at frame word 1; `n` and `n_len` into `r4` and `r6`, and `n`
checked: Z if it is valid. -/
def entry : List Instr :=
  [.addSp .r12 0, .str .r0 .r12 oP, .ldrSp .r4 aoN, .ldrSp .r6 aoK] ++ modulusCheck

/-- Zeros to the output whose pointer is at frame byte `o`. -/
def zeroOut (o : Nat) : Prog isa := .seq (.block [.ldrSp .r0 o, .ldrSp .lr aoK, .mov .r2 (.imm 0)]) maskBytes

/-- Zeros to `p` and `q`, and 0 returned. -/
def fail : Prog isa := seqs [zeroOut oP, zeroOut oQ, .block [.mov .r0 (.imm 0)]]

/-! ## The numbers -/

/-- `w = 2 ⌈n_len / 8⌉ + 2`, the stride, `w` into the division's header,
and every array zeroed. -/
def setupK : List Instr :=
  ctxB ++ [.ldrSp .r9 aoK, .dp .add .r9 .r9 (.imm 7), .mov .r9 (.shifted .r9 .lsr 3),
    .mov .r9 (.shifted .r9 .lsl 1), .dp .add .r9 .r9 (.imm 2)] ++ stride ++
  [.str .r9 .r8 16, .dp .add .r0 .r8 (.imm (BitVec.ofNat 32 hdr)), .mov .lr (.imm (BitVec.ofNat 32 nArr)),
    .mul .lr .lr .r7, .mov .lr (.shifted .lr .lsr 2), .mov .r3 (.imm 0)]

/-- `[j] :=` the bytes of the stack arguments at `o` and `o + 4`. -/
def loadArg (o j : Nat) : List (Prog isa) := [.block [.ldrSp .r4 o, .ldrSp .r6 (o + 4)], CrtValues.load j]

/-- `n`, `e` and `d` read (`e` and `d` to the arrays `wE` and `wD` with `W`). -/
def loads : Prog isa := seqs ([.block setupK, zero] ++ loadArg aoN aN ++ loadArg aoE (2 * wE) ++
  loadArg aoD (2 * wD))

/-- The top word of `[j]` := `2^31`: `[j] = 2^(32 w - 1)` if it was zero. -/
def setTop (j : Nat) : List Instr :=
  ptr .r0 j ++ [.dp .add .r0 .r0 (.shifted .r9 .lsl 2), .dp .sub .r0 .r0 (.imm 4),
    .mov .r1 (.imm 0x80000000), .str .r1 .r0 0]

/-- With `W`: the modulus `2^(32 W - 1)`, and `8 e_len` steps. -/
def prodSet : List Instr := ctxW ++ setTop wMod ++ [.ldrSp .r6 aoEl, .mov .r6 (.shifted .r6 .lsl 3)]

/-- `M := d e`. -/
def prod : Prog isa := .seq (.block prodSet) (mulMod wZ wE wD wM wMod wT)

/-- The low bit of `M` into `sBit`, and `M`'s cleared. -/
def skipBits : List Instr := bitOf sBit wM ++ clrLow wM

/-- Z iff `M` was odd and `m = M - 1` is not zero (`0 - m` borrows). -/
def skipTest : List Instr := [.ldr .r1 .r8 sBit, .dp .and .r1 .r1 (.reg .r11), .cmp .r1 (.imm 1)]

/-- `M = d e`, and whether to try candidates. -/
def numbers : Prog isa := seqs [loads, prod, .block skipBits, sub3 wT wZ wM, .block skipTest]

/-! ## `m = 2^t r` -/

/-- `c = 8 (d_len + e_len)` into `sCnt`. -/
def cntBits : List Instr :=
  [.ldrSp .r1 aoEl, .ldrSp .r2 aoDl, .dp .add .r1 .r1 (.reg .r2), .mov .r1 (.shifted .r1 .lsl 3), .str .r1 .r8 sCnt]

/-- `r := m`, `t := 0`, and the count. -/
def halfInit : Prog isa := seqs [copy wR wM, .block ([.mov .r1 (.imm 0), .str .r1 .r8 sTc] ++ cntBits)]

/-- The bit of `m` even into `sBit`, and `t +=` it. -/
def halfBit : List Instr :=
  bitOf sBit wR ++ [.ldr .r1 .r8 sBit, .dp .eor .r1 .r1 (.imm 1), .str .r1 .r8 sBit,
    .ldr .r2 .r8 sTc, .dp .add .r2 .r2 (.reg .r1), .str .r2 .r8 sTc]

/-- The count decremented: Z when it reaches 0. -/
def cntNext : List Instr := [.ldr .r1 .r8 sCnt, .subs .r1 .r1 (.imm 1), .str .r1 .r8 sCnt]

/-- A halving: `m := m / 2` and `t += 1` if `m` is even. -/
def halfBody : Prog isa := seqs [copy wU wR, copy wH wR, .block [.mov .r11 (.imm 0)], half wH,
  .block halfBit, sel wR wU wH sBit, .block cntNext]

def halving : Prog isa := .seq halfInit (.loop halfBody .ne)

/-! ## Montgomery multiplication's working space -/

/-- Its base into frame word 0 and `r0`, `⌈n_len / 8⌉` into `r7`, and `r3 = 0`. -/
def montSet : List Instr :=
  ptr .r0 mBase ++ [.dp .sub .r0 .r0 (.imm 256), .addSp .r12 0, .str .r0 .r12 0,
    .ldrSp .r7 aoK, .dp .add .r7 .r7 (.imm 7), .mov .r7 (.shifted .r7 .lsr 3), .mov .r3 (.imm 0)]

/-- The words above the low `w - 2` of `[j]` cleared. -/
def clrTop (j : Nat) : List Instr :=
  ptr .r0 j ++ [.dp .add .r0 .r0 (.shifted .r9 .lsl 2), .dp .sub .r0 .r0 (.imm 8), .mov .r1 (.imm 0),
    .str .r1 .r0 0, .str .r1 .r0 4]

/-- A Montgomery product `[o] := [a] [b] R⁻¹ mod n` (Montgomery indices),
then the context and `[o]`'s top words cleared. -/
def mmul (o a b : Nat) : List (Prog isa) := [.block mont0, selectedMontOp o a b, .block (ctx ++ clrTop (mBase + o))]

/-- The numbers 0 (`n - n`) and 1, and the base of the working space. -/
def montA : Prog isa := seqs [.block ctxw, sub3 aZ aN aN, copy aOne aZ, .block (setOne aOne ++ montSet)]

/-- `R² mod n` with its top words cleared; `R mod n` (from `1 · R²`) and
`n - R mod n`. -/
def montC : Prog isa := seqs [.block (ctx ++ clrTop mR2), copy mXm aOne, seqs (mmul iXm iXm iR2), copy aO mXm,
  sub3 aNg aN aO]

/-- The numbers 0 and 1, the working space, `n` and `R² mod n`, `R mod n`
and `n - R mod n`. -/
def mont : Prog isa := seqs [montA, setup, .block [.ldrSp .r4 aoN, .ldrSp .r6 aoK], precompute, montC]

/-! ## A candidate -/

/-- `g = sCand + 2` into `[mG]`, `y := 1` (in Montgomery form), `r`'s copy
and the count of its bits. -/
def candSet : Prog isa := seqs [copy mG aZ,
  .block (ptr .r0 mG ++ [.ldr .r1 .r8 sCand, .dp .add .r1 .r1 (.imm 2), .str .r1 .r0 0]),
  copy mY aO, .block ctxW, copy wRc wR, .block (cntBits ++ ctxw)]

/-- A bit of `r`: the multiplicand `g^(2^i)` or 1, by the bit of `r`'s copy
shifted out; `y` times it, and `g^(2^i)` squared. -/
def expBody : Prog isa := seqs ([.block (ctxW ++ bitOf sBit wRc ++ [.mov .r11 (.imm 0)]), half wRc,
  .block ctxw, sel mXm aO mG sBit, seqs (mmul iY iY iXm), seqs (mmul iG iG iG), .block cntNext])

/-- `y` to the power `r`. -/
def expLoop : Prog isa := .loop expBody .ne

/-- `[a] = [b]` into the slot `d`. -/
def eqAt (d a b : Nat) : Prog isa := eqS d a b aW

/-- `done := (y = 1) ∨ (y = -1)`, `ok := 0`, `k := 0`, and the count. -/
def sqInit : List Instr :=
  [.ldr .r1 .r8 sE1, .ldr .r2 .r8 sE2, .dp .orr .r1 .r1 (.reg .r2), .str .r1 .r8 sDone,
    .mov .r1 (.imm 0), .str .r1 .r8 sOk, .str .r1 .r8 sK] ++ cntBits

/-- After `x = y²`, with `x = 1` in `sE1` and `x = -1` in `sE2`: the
squaring is live if not done and `k < t`; it finds `y` if `x = 1`, stops if
`x = -1` or `k + 1 = t`, and otherwise `y := x` (`sLive`). -/
def sqMasks : List Instr :=
  [.ldr .r1 .r8 sK, .ldr .r2 .r8 sTc, .dp .sub .r3 .r1 (.reg .r2), .mov .r3 (.shifted .r3 .lsr 31),
    .ldr .r4 .r8 sDone, .dp .eor .r5 .r4 (.imm 1), .dp .and .r3 .r3 (.reg .r5),
    .dp .add .r1 .r1 (.imm 1), .dp .eor .r1 .r1 (.reg .r2), .dp .sub .r1 .r1 (.imm 1),
    .mov .r1 (.shifted .r1 .lsr 31), .ldr .r2 .r8 sE2, .dp .orr .r1 .r1 (.reg .r2),
    .ldr .r2 .r8 sE1, .ldr .r5 .r8 sOk, .dp .and .r10 .r3 (.reg .r2), .dp .orr .r5 .r5 (.reg .r10),
    .str .r5 .r8 sOk,
    .dp .orr .r10 .r2 (.reg .r1), .dp .and .r10 .r10 (.reg .r3), .dp .orr .r4 .r4 (.reg .r10),
    .str .r4 .r8 sDone,
    .dp .eor .r10 .r10 (.imm 1), .dp .and .r10 .r10 (.reg .r3), .str .r10 .r8 sLive]

/-- `k += 1`, and the count. -/
def sqNext : List Instr := [.ldr .r1 .r8 sK, .dp .add .r1 .r1 (.imm 1), .str .r1 .r8 sK] ++ cntNext

/-- A squaring under the masks. -/
def sqBody : Prog isa := seqs ([seqs (mmul iX iY iY), eqAt sE1 mX aO, eqAt sE2 mX aNg, .block sqMasks,
  copy aU mY, sel mY aU mX sLive, .block sqNext])

def sqLoop : Prog isa := .loop sqBody .ne

/-- The candidates tried `+= 1`, and `r1` nonzero to go on: fewer than 100
tried and not `ok`. Z if not. -/
def candNext : List Instr :=
  [.ldr .r1 .r8 sCand, .dp .add .r1 .r1 (.imm 1), .str .r1 .r8 sCand, .dp .sub .r1 .r1 (.imm 100),
    .mov .r1 (.shifted .r1 .lsr 31), .ldr .r2 .r8 sOk, .dp .eor .r2 .r2 (.imm 1),
    .dp .and .r1 .r1 (.reg .r2), .subs .r1 .r1 (.imm 0)]

/-- A candidate. -/
def candBody : Prog isa := seqs ([candSet, seqs (mmul iG iG iR2), expLoop, eqAt sE1 mY aO, eqAt sE2 mY aNg,
  .block sqInit, sqLoop, .block candNext])

/-- The candidates, from `sCand = 0`. -/
def candLoop : Prog isa :=
  .seq (.block [.mov .r1 (.imm 0), .str .r1 .r8 sCand]) (.loop candBody .ne)

/-! ## The factors -/

/-- `ok` into the mask, and `y` out of Montgomery form. -/
def finY : Prog isa := seqs [.block [.ldr .r1 .r8 sOk, .str .r1 .r8 sMask], copy mXm aOne,
  seqs (mmul iY iY iXm)]

/-- `inverse`'s start: `(u, v, x₁, x₂) = (y - 1, n, 1, 0)`, its modulus `n`,
the negated modulus and zero. -/
def gcdSet : Prog isa := seqs [sub3 0 mY aOne, copy 1 aN, copy aM aN, copy 2 aZ, .block (setOne 2),
  copy 3 aZ, copy aZero aZ, sub3 aNM aZero aM]

/-- The word above the `w` of `[j]` cleared, as the division's divisor needs. -/
def clrW (j : Nat) : List Instr :=
  ptr .r0 j ++ [.dp .add .r0 .r0 (.shifted .r9 .lsl 2), .mov .r1 (.imm 0), .str .r1 .r0 0]

/-- The division of `n` by `p` set up. -/
def divSet : Prog isa := seqs [copy aQ aN, copy aDv 1, .block (clrW aDv ++ CrtValues.divHdr aQ aRm aDv aDt)]

/-- `p < q` into `sLt`, and the larger into 5, the smaller into 6. -/
def order : Prog isa := seqs [.block ctxw, sub3 aW 1 aQ, .block [.str .r11 .r8 sLt], sel 5 1 aQ sLt,
  sel 6 aQ 1 sLt]

/-- The factors written out under the mask, and the mask returned. -/
def stores : Prog isa := seqs [
  .block [.ldrSp .r10 oP, .ldrSp .r11 aoK], CrtValues.store 5,
  .block [.ldrSp .r10 oQ, .ldrSp .r11 aoK], CrtValues.store 6,
  .block [.ldr .r0 .r8 sMask]]

def fin : Prog isa := seqs [finY, gcdSet, inverse, divSet, Rsa.Arm.Div.code, order, stores]

/-- Once `M` is known odd and above 1. -/
def rest : Prog isa := seqs [halving, mont, candLoop, fin]

/-- Once `n` is known valid. -/
def validWith (work : Prog isa) : Prog isa := .seq numbers (.ite .eq work fail)

def valid : Prog isa := validWith rest

/-- `vg_rsa_recover_primes`. -/
def codeWith (body : Prog isa) : Prog isa :=
  .frame (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (.seq (.block entry) (.seq body (.block PcFn.restore))) (.pop .r12 56)

/-- The original recovery body in the shared ABI wrapper. -/
def code : Prog isa := codeWith (.ite .eq valid fail)

end VG.Impl.Rsa.Arm.Recover
