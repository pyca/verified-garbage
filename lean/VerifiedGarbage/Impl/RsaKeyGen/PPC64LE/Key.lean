module

public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Ops
public import VerifiedGarbage.Impl.Rsa.PPC64LE.CrtValues

/-! # An RSA key from its two primes on PPC64LE

`vg_rsa_keygen_key(n, n_len, d, d_len, p, p_len, q, q_len, dp, dp_len, dq,
dq_len, qinv, qinv_len, e, e_len, scratch, scratch_len)`: the first eight
arguments in `r3`–`r10`, the others on the stack, at `sp + 96 + 8 i` for the
`i`-th of them (`dp` is the 0th).

The numbers live in the working space of the RSA key operations at
`scratch` (`Impl/Rsa/PPC64LE/KeyWs.lean`) with `w = p_len / 2` digits of 32
bits: room for `n`, of `16 p_len` bits, and for every other number. The
pointers and lengths stay in the nonvolatile `r14`–`r24` (`n`, `d`, `p`, `q`,
`dp`, `dq`, `qinv`, `e`, `p_len`, `e_len`, `n_len`), saved with `r29`–`r31` in
the header, as `vg_rsa_crt_values` does (`Impl/Rsa/PPC64LE/CrtValues.lean`).
Then, as ARMv7 computes the key (`Impl/RsaKeyGen/Arm/Key.lean`):

1. `p` and `q` swapped, by selections under the borrow of `p - q`, so that
   `p ≥ q`; `p - 1` and `q - 1` (0 for 0).
2. `L = lcm(p - 1, q - 1)`: their product `φ` (`mul`, over `8 p_len` bits);
   `8 p_len` steps that halve `u`, `v` (copies of `p - 1` and `q - 1`) and `φ`
   while `u` and `v` are both even; `v` made odd by a swap (if it is even);
   `gcd(u, v)` by `invOf` (modulo `v`, or 3 for `v < 2`; at the primes'
   width) and 1 for `v < 2`;
   and `φ` divided by it (`Impl/Rsa/PPC64LE/Div.lean`).
3. `d = e⁻¹ mod L`, and the flag of its existence, for every case of `e`,
   selected by masks of whether `e` is odd and whether it is 1, without
   branches:
   * `e` odd and at least 3 (with the modulus 3 otherwise): `L = e Q + R`,
     `x = R⁻¹ mod e` by `invOf` (two digits), `t = e - x` and
     `d = Q t + (R t + 1) / e` (`Proof/RsaKeyGen/OddInverseQuotient.lean`),
     whose products fit `w` digits;
   * `e = 1`: `d = 1`, for `L ≠ 1`;
   * `e` even: `d = e⁻¹ mod L` by `invOf` (`w` digits) for an odd `L ≥ 3` (the modulus
     3 otherwise), which `e = 0` never has.
4. Whether `d` exists and `d ≤ 2^(8 p_len)`: the status 2.
5. `qInv` by `invOf` (modulo `p`, or 3 for a `p` even or below 3; at the
   primes' width),
   `dP = d mod (p - 1)` and `dQ = d mod (q - 1)` by the division (by 1 for
   `p - 1` or `q - 1` zero, which the mask then rules out), and `n = p q` by
   `mul`; the mask of the existence of `d`, `gcd(q, p) = 1`,
   `n ≥ 2^(16 p_len - 1)`, `p` and `q` odd and `e` valid (odd, at least 3 and
   below `2^33`), and of the status not being 2.
6. The seven outputs written under the mask (`CrtValues.storeBytes`), and the
   status `mask + 2 small` returned.

Every choice is a selection (`sel`, `selS`) or a flag computed with `and`
and `xor`; addresses and loop counts depend only on the pointers and the
lengths, and there is no branch but the loops'.
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.PPC64LE.Key

open VG.PPC64LE VG.Impl.Rsa.PPC64LE.Keys VG.Impl.Rsa.PPC64LE.Div
open VG.Impl.Rsa.PPC64LE.CrtValues (stackArg load storeBytes restore)

/-! ## The arrays

0–14 are the inverse's (`aM` its modulus; `aZero` zero, which it leaves); then the constants, the inputs and the numbers. `aDv` is the
division's divisor: only copies write it, so its extra digit stays 0. -/

def aOne : Nat := 15
def aTwo : Nat := 16
def aThree : Nat := 17
/-- `2^(32 w - 1)`. -/
def aTop : Nat := 18
/-- `2^(8 p_len) + 1`. -/
def aC : Nat := 19
/-- `2^33`. -/
def aC33 : Nat := 20
def aE : Nat := 21
def aP0 : Nat := 22
def aQ0 : Nat := 23
def aP : Nat := 24
def aQ : Nat := 25
def aPm : Nat := 26
def aQm : Nat := 27
def aT : Nat := 28
def aS : Nat := 29
def aU : Nat := 30
def aV : Nat := 31
def aF : Nat := 32
def aU2 : Nat := 33
def aV2 : Nat := 34
def aG : Nat := 35
def aL : Nat := 36
def aDv : Nat := 37
def aDr : Nat := 38
def aDt : Nat := 39
def aME : Nat := 40
def aQd : Nat := 41
def aR : Nat := 42
def aTt : Nat := 43
def aQt : Nat := 44
def aRt : Nat := 45
def aNc : Nat := 46
def aDo : Nat := 47
def aMl : Nat := 48
def aD : Nat := 49
def aDP : Nat := 50
def aDQ : Nat := 51
def aQi : Nat := 52
def aN : Nat := 53
def aMq : Nat := 54
def aMo : Nat := 55
def aMa : Nat := 56
def aMb : Nat := 57
def aMm : Nat := 58
def aMn : Nat := 59
/-- The number of arrays. -/
def nArr : Nat := 60

/-! ## The header

Bytes 0–111 hold `r14`–`r24` and `r29`–`r31` (as `vg_rsa_crt_values`'s),
124–132 the shared routines' slots; the flags are in `X0`–`X8`. -/

def X0 : Nat := 112
def X1 : Nat := 116
def X2 : Nat := 120
def X3 : Nat := 136
def X4 : Nat := 140
def X5 : Nat := 144
def X6 : Nat := 148
def X7 : Nat := 152
def X8 : Nat := 156

/-! ## Entry -/

/-- The working space's base into `r11`, the registers saved there, the
base into `r31`, and the pointers and lengths into `r14`–`r24`. -/
def entry : List Instr :=
  stackArg .r11 8 ++
  [.store .d .r14 .r11 0, .store .d .r15 .r11 8, .store .d .r16 .r11 16, .store .d .r17 .r11 24,
    .store .d .r18 .r11 32, .store .d .r19 .r11 40, .store .d .r20 .r11 48, .store .d .r21 .r11 56,
    .store .d .r22 .r11 64, .store .d .r23 .r11 72, .store .d .r24 .r11 80, .store .d .r29 .r11 88,
    .store .d .r30 .r11 96, .store .d .r31 .r11 104, .addi .r31 .r11 0,
    .addi .r14 .r3 0, .addi .r15 .r5 0, .addi .r16 .r7 0, .addi .r17 .r9 0, .addi .r22 .r8 0,
    .addi .r24 .r4 0] ++
  stackArg .r18 0 ++ stackArg .r19 2 ++ stackArg .r20 4 ++ stackArg .r21 6 ++ stackArg .r23 7

/-! ## Setup and the inputs -/

/-- `w = p_len / 2` into `r29`, the stride into `r30`, and every array zeroed. -/
def setup : Prog isa :=
  .seq (.block ([.lsr .d .r29 .r22 1] ++ stride ++ [.li .r8 nArr, .mul .r8 .r8 .r30, .lsr .d .r8 .r8 2]))
    (zeroArrays .r8)

/-- `p`, `q` and `e` read. -/
def loads : Prog isa := seqs [
  .block [.addi .r6 .r16 0, .addi .r8 .r22 0], load aP0,
  .block [.addi .r6 .r17 0, .addi .r8 .r22 0], load aQ0,
  .block [.addi .r6 .r21 0, .addi .r8 .r23 0], load aE]

/-- The constants 1, 2, 3, `2^(32 w - 1)`, `2^(8 p_len) + 1` and `2^33`. -/
def consts : List (Prog isa) := [
  .block ([.li .r6 0] ++ setDigit aOne 1 ++ setDigit aTwo 2 ++ setDigit aThree 3 ++ setDigit aC 1 ++
    [.addi .r6 .r22 0] ++ setDigit aC 1 ++ [.li .r6 4] ++ setDigit aC33 2 ++ [.li .r9 1]),
  half aTop]

/-! ## The primes -/

/-- The slot `d` := `[a] < [b]`, the borrow of `[a] - [b]` (`[aT]` scratch). -/
def ltS (d a b : Nat) : List (Prog isa) := [sub3 aT a b, .block (stBorrow d)]

/-- `p ≥ q`, `p - 1` and `q - 1`. -/
def primes : Prog isa := seqs (ltS X0 aP0 aQ0 ++ [sel aP aP0 aQ0 X0, sel aQ aQ0 aP0 X0] ++
  ltS X0 aP aOne ++ [sel aPm aT aZero X0] ++ ltS X0 aQ aOne ++ [sel aQm aT aZero X0])

/-! ## Products -/

/-- `[o] := ([a] ([b] mod 2^K)) mod 2^(32 w)` for `K` in `r11`. -/
def mulTo (o a b : Nat) (k : List Instr) : Prog isa :=
  seqs [copy aMa a, copy aMb b, copy aMo aZero, .block k, mulLoop aMo aMa aMb aMm aMn aZero sOdd, copy o aMo]

/-- `r11 := 8 p_len`. -/
def cnt8 : List Instr := [.lsl .r11 .r22 3]

/-! ## `lcm(p - 1, q - 1)` -/

/-- `[j]` halved under the slot `X2` (through `aT`). -/
def halfSel (j : Nat) : List (Prog isa) := [copy aT j, .block [.li .r9 0], half aT, sel j j aT X2]

/-- One step of the halving: `X2` the mask of `u` and `v` both even. -/
def halfStep : Prog isa := seqs ([.block (bitOf X0 aU ++ bitOf X1 aV ++ notS X1 X1 ++ andNotS X2 X0 X1)] ++
  halfSel aU ++ halfSel aV ++ halfSel aF ++ [.block [.subi .r11 .r11 1]])

/-- `φ`, and `8 p_len` steps of the halving. -/
def halving : Prog isa :=
  seqs [mulTo aF aPm aQm cnt8, copy aU aPm, copy aV aQm, .block cnt8, .loop halfStep (.nonzero .d .r11)]

/-- `[a]` modulo `[m]` by the batched inverse (`Impl/Rsa/PPC64LE/InvBatch.lean`):
`a` into array 0 and `m` into `aM`, and `k` sets its width, `r11` digits. -/
def invOf (a m : Nat) (k : List Instr) : Prog isa :=
  seqs [copy aM m, copy 0 a, .block k, VG.Impl.Rsa.PPC64LE.InvBatch.inverse]

/-- The width of the primes, `p_len / 4` digits. -/
def nP : List Instr := [.lsr .d .r11 .r22 2]

/-- Two digits, for numbers below `2^64`. -/
def nTwo : List Instr := [.li .r11 2]

/-- The full width, `w` digits. -/
def nW : List Instr := [.addi .r11 .r29 0]

/-- `v` odd by a swap, `[aG] := gcd(u, v)` (1 for `v < 2`). -/
def gcdUV : Prog isa := seqs ([.block (bitOf X0 aV ++ notS X0 X0), sel aU2 aU aV X0, sel aV2 aV aU X0] ++
  ltS X1 aV2 aTwo ++ [sel aS aV2 aThree X1, invOf aU2 aS nP, sel aG 1 aOne X1])

/-- `[q] := [q] / [d]` (`[aDr]` := the remainder), through `aDv`. -/
def divBy (q d : Nat) : Prog isa := seqs [copy aDv d, div q aDr aDv aDt]

/-- `[aL] := lcm(p - 1, q - 1)`. -/
def lcmPart : Prog isa := seqs [halving, gcdUV, copy aL aF, divBy aL aG]

/-! ## `d = e⁻¹ mod L`

The flags: `X3` `e` odd, `X4` `e = 1`, `X5` `e < 3`; then `X6` whether `d`
exists. -/

/-- The flags of `e`. -/
def eFlags : Prog isa := seqs ([.block (bitOf X3 aE), eqS X4 aE aOne] ++ ltS X5 aE aThree)

/-- `e` odd and at least 3 (modulus `mE`, `e` or 3): `L = mE Q + R`,
`x = R⁻¹ mod mE`, `t = mE - x`, `[aDo] := Q t + (R t + 1) / mE`, and
`X6` := `L ≥ 2` and `gcd(R, mE) = 1`. -/
def dOdd : Prog isa := seqs ([.block (andNotS X0 X5 X3), sel aME aThree aE X0, copy aQd aL, copy aDv aME,
  div aQd aR aDv aDt, invOf aR aME nTwo, eqS X1 1 aOne, sub3 aTt aME 3,
  mulTo aQt aQd aTt [.li .r11 64], mulTo aRt aR aTt [.li .r11 64], addTo aRt aOne aNc aZero,
  div aRt aDr aDv aDt, copy aDo aQt, addTo aDo aRt aNc aZero] ++ ltS X2 aL aTwo ++
  [.block (andNotS X6 X2 X1)])

/-- `e = 1`: `X7` := `L ≠ 1`; `X6` and `[aS]` the odd case's or `e = 1`'s. -/
def dOne : Prog isa := seqs [eqS X0 aL aOne, .block (notS X7 X0 ++ selS X6 X6 X7 X4), sel aS aDo aOne X4]

/-- `e` even (modulus `mL`, `L` if it is odd and at least 3, else 3):
`d = e⁻¹ mod mL`, and `X1` := `L` odd, at least 3, and `gcd(e, mL) = 1`;
then `[aD]` and `X6` by whether `e` is odd. -/
def dEven : Prog isa := seqs ([.block (bitOf X0 aL)] ++ ltS X1 aL aThree ++
  [.block (andNotS X2 X1 X0), sel aMl aThree aL X2, invOf aE aMl nW, eqS X0 1 aOne,
    .block (andS X1 X2 X0 ++ selS X6 X1 X6 X3), sel aD 3 aS X3])

/-- `d` and `X6`. -/
def dPart : Prog isa := seqs [eFlags, dOdd, dOne, dEven]

/-- `X7` := `X6` and `d ≤ 2^(8 p_len)` (`d < 2^(8 p_len) + 1`). -/
def smallPart : Prog isa := seqs (ltS X0 aD aC ++ [.block (andS X7 X0 X6)])

/-! ## The key -/

/-- `qInv` into `aQi` (modulo `p`, or 3 for a `p` even or below 3), `X0` `p`
odd, and `X1` the flag of `gcd(q, p) = 1`. -/
def qinvPart : Prog isa := seqs ([.block (bitOf X0 aP)] ++ ltS X1 aP aThree ++
  [.block (andNotS X2 X1 X0), sel aMq aThree aP X2, invOf aQ aMq nP, eqS X1 1 aOne, copy aQi 3])

/-- `[o] := d mod [j]`, by 1 for `[j] = 0`. -/
def crtOf (o j : Nat) : Prog isa :=
  seqs [eqS X2 j aZero, sel aS j aOne X2, copy aQd aD, copy aDv aS, div aQd o aDv aDt]

/-- `dP` into `aDP` and `dQ` into `aDQ`. -/
def crtPart : Prog isa := seqs [crtOf aDP aPm, crtOf aDQ aQm]

/-- `n = p q` into `aN`. -/
def nPart : Prog isa := mulTo aN aP aQ cnt8

/-- The mask of the checks into `X8`. -/
def maskPart : Prog isa := seqs (ltS X2 aN aTop ++ [.block (andNotS X8 X2 X6 ++ andS X8 X8 X1 ++ andS X8 X8 X0 ++
  bitOf X2 aQ ++ andS X8 X8 X2 ++ andS X8 X8 X3)] ++ ltS X2 aE aC33 ++
  [.block (andNotS X4 X5 X2 ++ andS X8 X8 X4 ++ andNotS X8 X7 X8)])

/-- The mask `0 - [X8]` into `r9`. -/
def mask : List Instr := [.load .w .r9 .r31 X8, .li .r0 0, .sub .r9 .r0 .r9]

/-- The array `j`'s low bytes to the output at `rP`, `rL` bytes, under the mask. -/
def storeTo (rP rL : Reg) (j : Nat) : List (Prog isa) :=
  [.block ([.addi .r5 rP 0, .addi .r8 rL 0] ++ mask), storeBytes j]

/-- The seven outputs under the mask, and the status `mask + 2 small`. -/
def stores : Prog isa := seqs (storeTo .r14 .r24 aN ++ storeTo .r15 .r24 aD ++ storeTo .r16 .r22 aP ++
  storeTo .r17 .r22 aQ ++ storeTo .r18 .r22 aDP ++ storeTo .r19 .r22 aDQ ++ storeTo .r20 .r22 aQi ++
  [.block [.load .w .r3 .r31 X7, .lsl .r3 .r3 1, .load .w .r0 .r31 X8, .add .r3 .r3 .r0]])

def body : Prog isa :=
  seqs ([setup, loads] ++ consts ++ [primes, lcmPart, dPart, smallPart, qinvPart, crtPart, nPart, maskPart, stores])

/-- `vg_rsa_keygen_key`. -/
def code : Prog isa := .seq (.block entry) (.seq body (.block restore))

end VG.Impl.RsaKeyGen.PPC64LE.Key
