module

public import VerifiedGarbage.Impl.Rsa.RISCV64.Div
public import VerifiedGarbage.Impl.Rsa.RISCV64.Inverse
public import VerifiedGarbage.Impl.Bignum.RISCV64.Precompute

/-!
# `vg_rsa_crt_values` on RISC-V

`vg_rsa_crt_values(dp = a0, dp_len = a1, dq = a2, dq_len = a3, qinv = a4,
qinv_len = a5, n = a6, n_len = a7, p, p_len, q, q_len, d, d_len, scratch,
scratch_len)`, the last eight on the stack. As on PPC64LE
(`Impl/Rsa/PPC64LE/CrtValues.lean`), in words of 64 bits:

* `n` is checked as `vg_rsa_public_precompute` checks it
  (`Precompute.check`), the only branch on data; an invalid modulus writes
  zeros to the three outputs and returns 0.
* `p q = n`: `p` odd, `n / p = q` and `n mod p = 0`, by the fixed-iteration
  division (`Impl/Rsa/RISCV64/Div.lean`).
* `qInv` is the inverse of `q` modulo `p | 1` (`Impl/Rsa/RISCV64/Inverse.lean`),
  which exists if the gcd it computes is 1. It runs in a working space of
  the primes' words `w' = ⌈max(p_len, q_len) / 8⌉` (`s9`, computed without
  a branch, and its stride in `s10`), which `q` and `p` are read into
  again, for `4 (p_len + q_len)` iterations of two steps:
  `q (p | 1) < 2^(8 (p_len + q_len))`. Its 16 arrays end before array 16
  of the working space of `w` words, which holds what the rest needs; `qInv`
  is written out from there.
* `dP` and `dQ` are the remainders of `d` divided by `p` and by `q` with
  their low bits cleared: `p - 1` and `q - 1` for odd primes, which `p q = n`
  makes them.

The results are written under the mask of the checks, which is returned.

Registers kept throughout: `s1` `n`, `s2` `n_len`, `s3` `p`, `s4` `p_len`,
`s5` `q`, `s6` `q_len`, `a0` `d`, `a1` `d_len`, `a2` `dp`, `a3` `dq`, `a6`
`qinv`; `s9`–`s11` the working space's (`Impl/Rsa/RISCV64/KeyWs.lean`), `s7`
the count of the divisions and the inverse, and `s0` the working space's `w`
during the inverse.
-/

@[expose] public section

namespace VG.Impl.Rsa.RISCV64.CrtValues

open VG.RISCV64 VG.Impl.Bignum.RISCV64 VG.Impl.Rsa.RISCV64.Keys VG.Impl.Rsa.RISCV64.Div

/-! ## The header -/

def sPodd : Nat := 152
def sE1 : Nat := 160
def sE2 : Nat := 168
def sE3 : Nat := 176
def sMask : Nat := 184

/-! ## The arrays

0–14 are `inverse`'s and 15 its `1`, all in the working space of `w'`
words; then `q`, `p`, the division's quotient, remainder, divisor and
temporary, the remainders kept for `dP` and `dQ`, and `d`. -/

def aOne : Nat := 15
def aQ : Nat := 16
def aP : Nat := 17
def aDQ : Nat := 18
def aDR : Nat := 19
def aDD : Nat := 20
def aDT : Nat := 21
def aDR2 : Nat := 22
def aDR3 : Nat := 23
def aD : Nat := 24

/-- The number of arrays. -/
def nArr : Nat := 25

/-! ## Entry -/

/-- The working space (the stack argument 6) and the registers saved there,
then the pointers and lengths into the registers kept. -/
def entry : List Instr :=
  save 48 ++
  [mov .s1 .a6, mov .s2 .a7, mov .a6 .a4, mov .a3 .a2, mov .a2 .a0, .addSp .t0 0,
    .load .d .s3 .t0 0, .load .d .s4 .t0 8, .load .d .s5 .t0 16, .load .d .s6 .t0 24,
    .load .d .a0 .t0 32, .load .d .a1 .t0 40]

/-- Whether `n` is a valid modulus, in `s0`: 0 if it is (`Precompute.check`,
from `n` in `s7` and `n_len` in `s8`). -/
def nCheck : Prog isa := .seq (.block [mov .s7 .s1, mov .s8 .s2]) Precompute.check

/-! ## An invalid modulus -/

/-- Zeros to `dp`, `dq` and `qinv`, and 0 returned. -/
def fail : Prog isa :=
  seqs [zeroBytes .a2 .s4, zeroBytes .a3 .s6, zeroBytes .a6 .s4, .block [.li .a0 0]]

/-! ## A valid modulus -/

/-- `w = ⌈n_len / 8⌉`, the stride, and every array zeroed. -/
def setup : Prog isa := .seq (.block (setW .s2)) (zeroArrays nArr)

/-- `n`, `p`, `q` and `d` read. -/
def loads : Prog isa := seqs [load aDQ .s1 .s2, load aP .s3 .s4, load aQ .s5 .s6, load aD .a0 .a1]

/-- `p` odd, `n` divided by `p`, and the checks `n / p = q` and `n mod p = 0`. -/
def checks : Prog isa := seqs [
  copy aDD aP, .block (bitOf sPodd aP), div aDQ aDR aDD aDT, eqS sE1 aDQ aQ, eqS sE2 aDR aZero]

/-- The arrays of the inverse, at the primes' words. -/
def nInv : Nat := 16

/-- `s0 := w`; then the working space of the primes' words, `s9 := w' =
⌈max(p_len, q_len) / 8⌉` without a branch (`p_len - ((p_len - q_len) &
mask)`, the mask all ones where `p_len < q_len`) and `s10 := 8 (w' + 2)`;
and `s7 := 4 (p_len + q_len)`. -/
def narrow : List Instr :=
  [mov .s0 .s9, .sltu .t6 .s4 .s6, .li .t5 0, .sub .t6 .t5 .t6, .sub .t5 .s4 .s6,
    .logic .and .t5 .t5 .t6, .sub .t5 .s4 .t5, .addi .t5 .t5 7, .shift .srl .d .s9 .t5 3,
    .addi .s10 .s9 2, .shift .sll .d .s10 .s10 3, .add .s7 .s4 .s6, .shift .sll .d .s7 .s7 2]

/-- The working space of `w = s0` words back. -/
def widen : List Instr := [mov .s9 .s0, .addi .s10 .s9 2, .shift .sll .d .s10 .s10 3]

/-- `inverse`'s start in the working space of `w'` words, its arrays 0–15
zeroed: `(u, v, x₁, x₂) = (q, m, 1, 0)` with `m = p | 1`, `[aOne] = 1`,
and `[aNM] = 2^(64 w') - m`. -/
def invSetup : List (Prog isa) := [
  zeroArrays nInv, load 0 .s5 .s6, load aM .s3 .s4, .block (orOne aM), copy 1 aM,
  .block (setOne 2 ++ setOne aOne), sub3 aNM aZero aM]

/-- The mask `0 - [sMask]` into `t4`. -/
def mask : List Instr := [.load .d .t4 .s11 sMask, .li .t5 0, .sub .t4 .t5 .t4]

/-- The checks' mask, the gcd's check and `qInv` written under it, at the
primes' words, which `inverse`'s arrays fit in: the arrays from 16 on, at
`w`'s stride, are past them. -/
def invPart : Prog isa := seqs ([.block narrow] ++ invSetup ++ [
  inverse, eqS sE3 1 aOne,
  .block (andS sMask sPodd sE1 ++ andS sMask sMask sE2 ++ andS sMask sMask sE3 ++ mask),
  storeBytes 3 .a6 .s4, .block widen])

/-- `d` divided by `p - 1` and by `q - 1`. -/
def dParts : Prog isa := seqs [
  copy aDQ aD, copy aDD aP, .block (clrLow aDD), div aDQ aDR2 aDD aDT,
  copy aDQ aD, copy aDD aQ, .block (clrLow aDD), div aDQ aDR3 aDD aDT]

def arith : Prog isa := seqs [checks, invPart, dParts]

/-- `dP` and `dQ` written out under the mask, and the mask's bit returned. -/
def stores : Prog isa := seqs [
  .block mask, storeBytes aDR2 .a2 .s4, storeBytes aDR3 .a3 .s6,
  .block [.load .d .a0 .s11 sMask]]

def valid : Prog isa := seqs [setup, loads, arith, stores]

/-- `vg_rsa_crt_values`. -/
def code : Prog isa :=
  .seq (.block entry) (.seq nCheck (.seq (.ite (.zero .s0) valid fail) (.block restore)))

end VG.Impl.Rsa.RISCV64.CrtValues
