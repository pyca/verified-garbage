module

public import VerifiedGarbage.Impl.RsaKeyGen.RISCV64.Ops

/-! # An RSA key from its two primes on RISC-V

`vg_rsa_keygen_key(n = a0, n_len = a1, d = a2, d_len = a3, p = a4,
p_len = a5, q = a6, q_len = a7, dp, dp_len, dq, dq_len, qinv, qinv_len, e,
e_len, scratch, scratch_len)`, the last ten on the stack, at `sp + 8 i` for
the `i`-th of them (`dp` is the 0th).

The numbers live in the working space of the RSA key operations at
`scratch` (`Impl/Rsa/RISCV64/KeyWs.lean`) with `w = p_len / 4` words of 64
bits: room for `n`, of `16 p_len` bits, and for every other number. The
pointers and lengths stay in registers no routine here writes: `s0` `n`,
`s1` `d`, `s2` `p`, `s3` `q`, `s4` `dp`, `s5` `dq`, `s6` `qinv`, `a0` `e`,
`a1` `p_len` and `a7` `e_len` (`n_len` is `2 p_len`); `s9`–`s11` are the
working space's, and `s7` counts. The caller's `s0`–`s11` are saved in the
header, as `vg_rsa_crt_values` saves them (`Impl/Rsa/RISCV64/CrtValues.lean`).

Then, step for step as PPC64LE computes the key
(`Impl/RsaKeyGen/PPC64LE/Key.lean`), with RISC-V's routines:

1. `p` and `q` swapped, by selections under the borrow of `p - q`, so that
   `p ≥ q`; `p - 1` and `q - 1` (0 for 0).
2. `L = lcm(p - 1, q - 1)`: their product `φ` (`mulTo`, the schoolbook
   product); `8 p_len` steps that halve `u`, `v` (copies of `p - 1` and
   `q - 1`) and `φ` while `u` and `v` are both even; `v` made odd by a swap
   (if it is even); `gcd(u, v)` by `invOf` (modulo `v`, or 3 for `v < 2`;
   `8 p_len` iterations) and 1 for `v < 2`; and `φ` divided by it
   (`Impl/Rsa/RISCV64/Div.lean`).
3. `d = e⁻¹ mod L`, and the flag of its existence, for every case of `e`,
   selected by masks of whether `e` is odd and whether it is 1, without
   branches:
   * `e` odd and at least 3 (with the modulus 3 otherwise): `L = e Q + R`,
     `x = R⁻¹ mod e` by `invOf` (64 iterations), `t = e - x` and
     `d = Q t + (R t + 1) / e` (`Proof/RsaKeyGen/OddInverseQuotient.lean`);
   * `e = 1`: `d = 1`, for `L ≠ 1`;
   * `e` even: `d = e⁻¹ mod L` by `invOf` (`8 p_len + 32` iterations) for an
     odd `L ≥ 3` (the modulus 3 otherwise), which `e = 0` never has. This
     inverse runs only for an even `e` (a branch on `e`'s parity, which the
     contract's leak includes).
4. Whether `d` exists and `d ≤ 2^(8 p_len)`: the status 2.
5. `qInv` by `invOf` (modulo `p`, or 3 for a `p` even or below 3; `8 p_len`
   iterations), `dP = d mod (p - 1)` and `dQ = d mod (q - 1)` by the
   division (by 1 for `p - 1` or `q - 1` zero, which the mask then rules
   out), and `n = p q` by `mulTo`; the mask of the existence of `d`,
   `gcd(q, p) = 1`, `n ≥ 2^(16 p_len - 1)`, `p` and `q` odd and `e` valid
   (odd, at least 3 and below `2^33`), and of the status not being 2.
6. The seven outputs written under the mask (`storeBytes`), and the status
   `mask + 2 small` returned.

Every choice is a selection (`sel`, `selS`) or a flag computed with `and`
and `xor`; addresses and loop counts depend only on the pointers and the
lengths, and the only branches are the loops' and the one on `e`'s parity
(public: the contract's leak includes `e`).
-/

@[expose] public section

namespace VG.Impl.RsaKeyGen.RISCV64.Key

open VG.RISCV64 VG.Impl.Rsa.RISCV64.Keys VG.Impl.Rsa.RISCV64.Div

/-! ## The arrays

0–14 are the inverse's (`aM` its modulus; `aZero` zero, which it leaves);
then the constants, the inputs and the numbers. `aDv` is the division's
divisor: only copies write it, so its extra word stays 0. -/

def aOne : Nat := 15
def aTwo : Nat := 16
def aThree : Nat := 17
/-- `2^(64 w - 1)`. -/
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
/-- `R t + 1`, then its quotient by `e`. -/
def aRp : Nat := 55
/-- The number of arrays. -/
def nArr : Nat := 56

/-! ## The header

Bytes 0–95 hold the caller's `s0`–`s11`, 128–144 the shared routines'
slots; the flags are in `X0`–`X8`. -/

def X0 : Nat := 152
def X1 : Nat := 160
def X2 : Nat := 168
def X3 : Nat := 176
def X4 : Nat := 184
def X5 : Nat := 192
def X6 : Nat := 200
def X7 : Nat := 208
def X8 : Nat := 216

/-! ## Entry -/

/-- The working space (the stack argument 8) and the registers saved there,
then the pointers and lengths into the registers kept. -/
def entry : List Instr :=
  save 64 ++
  [mov .s0 .a0, mov .s1 .a2, mov .s2 .a4, mov .s3 .a6, mov .a1 .a5, .addSp .t0 0,
    .load .d .s4 .t0 0, .load .d .s5 .t0 16, .load .d .s6 .t0 32, .load .d .a0 .t0 48,
    .load .d .a7 .t0 56]

/-! ## Setup and the inputs -/

/-- `w = 2 p_len / 8` into `s9`, the stride into `s10`, and every array zeroed. -/
def setup : Prog isa :=
  .seq (.block ([.shift .sll .d .t6 .a1 1] ++ setW .t6)) (zeroArrays nArr)

/-- `p`, `q` and `e` read. -/
def loads : Prog isa := seqs [load aP0 .s2 .a1, load aQ0 .s3 .a1, load aE .a0 .a7]

/-- The constants 1, 2, 3, `2^(8 p_len) + 1`, `2^33` and `2^(64 w - 1)`. -/
def consts : List (Prog isa) := [
  .block (setOne aOne ++ setLow aTwo 2 ++ setLow aThree 3 ++ setOne aC ++
    ptr .t0 aC ++ [.add .t0 .t0 .a1, .li .t5 1, .store .d .t5 .t0 0] ++
    ptr .t0 aC33 ++ [.li .t5 1, .shift .sll .d .t5 .t5 33, .store .d .t5 .t0 0, .li .t4 1]),
  half aTop]

/-! ## The primes -/

/-- The slot `d` := `[a] < [b]`, the borrow of `[a] - [b]` (`[aT]` scratch). -/
def ltS (d a b : Nat) : List (Prog isa) := [sub3 aT a b, .block (stBorrow d)]

/-- `p ≥ q`, `p - 1` and `q - 1`. -/
def primes : Prog isa := seqs (ltS X0 aP0 aQ0 ++ [sel aP aP0 aQ0 X0, sel aQ aQ0 aP0 X0] ++
  ltS X0 aP aOne ++ [sel aPm aT aZero X0] ++ ltS X0 aQ aOne ++ [sel aQm aT aZero X0])

/-! ## `lcm(p - 1, q - 1)` -/

/-- `s7 := 8 p_len`. -/
def cnt8 : List Instr := [.shift .sll .d .s7 .a1 3]

/-- `[j]` halved under the slot `X2` (through `aT`). -/
def halfSel (j : Nat) : List (Prog isa) := [copy aT j, .block [.li .t4 0], half aT, sel j j aT X2]

/-- One step of the halving: `X2` the mask of `u` and `v` both even. -/
def halfStep : Prog isa := seqs ([.block (bitOf X0 aU ++ bitOf X1 aV ++ notS X1 X1 ++ andNotS X2 X0 X1)] ++
  halfSel aU ++ halfSel aV ++ halfSel aF ++ [.block [.addi .s7 .s7 (-1)]])

/-- `φ`, and `8 p_len` steps of the halving. -/
def halving : Prog isa :=
  seqs [mulTo aF aPm aQm, copy aU aPm, copy aV aQm, .block cnt8, .loop halfStep (.nonzero .s7)]

/-- The digits of an inverse of numbers below `2^(8 p_len)`: `p_len / 4`. -/
def nP : List Instr := [.shift .srl .d .s8 .a1 2]

/-- The digits of an inverse of numbers below `2^64`: 2. -/
def nTwo : List Instr := [.li .s8 2]

/-- The digits of an inverse of a number below `2^64` modulo one below
`2^(16 p_len)`: `p_len / 2`. -/
def nW : List Instr := [.shift .srl .d .s8 .a1 1]

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
  mulTo aQt aQd aTt, mulTo aRt aR aTt, VG.Impl.Rsa.RISCV64.RecoverDet.add aRp aRt aOne aZero aNc,
  div aRp aDr aDv aDt, VG.Impl.Rsa.RISCV64.RecoverDet.add aDo aQt aRp aZero aNc] ++ ltS X2 aL aTwo ++
  [.block (andNotS X6 X2 X1)])

/-- `e = 1`: `X7` := `L ≠ 1`; `X6` and `[aS]` the odd case's or `e = 1`'s. -/
def dOne : Prog isa := seqs [eqS X0 aL aOne, .block (notS X7 X0 ++ selS X6 X6 X7 X4), sel aS aDo aOne X4]

/-- `e` even (modulus `mL`, `L` if it is odd and at least 3, else 3):
`d = e⁻¹ mod mL`, and `X1` := `L` odd, at least 3, and `gcd(e, mL) = 1`;
then `[aD]` and `X6` by whether `e` is odd. -/
def dEven : Prog isa := seqs ([.block (bitOf X0 aL)] ++ ltS X1 aL aThree ++
  [.block (andNotS X2 X1 X0), sel aMl aThree aL X2, invOf aE aMl nW, eqS X0 1 aOne,
    .block (andS X1 X2 X0 ++ selS X6 X1 X6 X3), sel aD 3 aS X3])

/-- `e` odd: `[aD] := [aS]` (what `dEven` gives for an odd `e`, without its
inverse); `e` even: `dEven`. The branch is on `e`'s parity, which the
contract's leak includes. -/
def dPar : Prog isa :=
  .seq (.block [.load .d .t5 .s11 X3]) (.ite (.nonzero .t5) (copy aD aS) dEven)

/-- `d` and `X6`. -/
def dPart : Prog isa := seqs [eFlags, dOdd, dOne, dPar]

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
def nPart : Prog isa := mulTo aN aP aQ

/-- The mask of the checks into `X8`. -/
def maskPart : Prog isa := seqs (ltS X2 aN aTop ++ [.block (andNotS X8 X2 X6 ++ andS X8 X8 X1 ++ andS X8 X8 X0 ++
  bitOf X2 aQ ++ andS X8 X8 X2 ++ andS X8 X8 X3)] ++ ltS X2 aE aC33 ++
  [.block (andNotS X4 X5 X2 ++ andS X8 X8 X4 ++ andNotS X8 X7 X8)])

/-- The mask `0 - [X8]` into `t4`. -/
def mask : List Instr := [.load .d .t4 .s11 X8, .li .t5 0, .sub .t4 .t5 .t4]

/-- The array `j`'s low bytes to the output at `rP`, `rL` bytes, under the mask. -/
def storeTo (rP rL : Reg) (j : Nat) : List (Prog isa) := [.block mask, storeBytes j rP rL]

/-- The seven outputs under the mask (`n_len = 2 p_len` in `a5`), and the
status `mask + 2 small`. -/
def stores : Prog isa := seqs ([.block [.shift .sll .d .a5 .a1 1]] ++
  storeTo .s0 .a5 aN ++ storeTo .s1 .a5 aD ++ storeTo .s2 .a1 aP ++
  storeTo .s3 .a1 aQ ++ storeTo .s4 .a1 aDP ++ storeTo .s5 .a1 aDQ ++ storeTo .s6 .a1 aQi ++
  [.block [.load .d .a0 .s11 X7, .shift .sll .d .a0 .a0 1, .load .d .t5 .s11 X8, .add .a0 .a0 .t5]])

def body : Prog isa :=
  seqs ([setup, loads] ++ consts ++ [primes, lcmPart, dPart, smallPart, qinvPart, crtPart, nPart, maskPart, stores])

/-- `vg_rsa_keygen_key`. -/
def code : Prog isa := .seq (.block entry) (.seq body (.block restore))

end VG.Impl.RsaKeyGen.RISCV64.Key
