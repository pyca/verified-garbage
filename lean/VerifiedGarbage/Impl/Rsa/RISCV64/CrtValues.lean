module

public import VerifiedGarbage.Impl.Rsa.RISCV64.Div
public import VerifiedGarbage.Impl.Rsa.RISCV64.InvBatch
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
  division (`Impl/Rsa/RISCV64/Div.lean`), whose steps pass over the
  divisor's `⌈p_len / 8⌉` words (`Div.divL`).
* `qInv` is the inverse of `q` modulo `p | 1` (`Impl/Rsa/RISCV64/InvBatch.lean`,
  by batches of divsteps), which exists if the gcd it computes is 1, on
  numbers of the primes' digits of 32 bits `⌈max(p_len, q_len) / 4⌉` (`s8`,
  computed without a branch), in arrays 0–14, which hold nothing the rest
  needs by then.
* `dP` and `dQ` are the remainders of `d` divided by `p` and by `q` with
  their low bits cleared: `p - 1` and `q - 1` for odd primes, which `p q = n`
  makes them; the divisions pass over `⌈p_len / 8⌉` and `⌈q_len / 8⌉` words.

The results are written under the mask of the checks, which is returned.

Registers kept throughout: `s1` `n`, `s2` `n_len`, `s3` `p`, `s4` `p_len`,
`s5` `q`, `s6` `q_len`, `a0` `d`, `a1` `d_len`, `a2` `dp`, `a3` `dq`, `a6`
`qinv`; `s9`–`s11` the working space's (`Impl/Rsa/RISCV64/KeyWs.lean`), `s7`
the count of the divisions and the inverse, and `s8` the inverse's digits,
then each division's words.
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

0–14 are `InvBatch.inverse`'s and 15 its `1` (10, zero, serves the checks
before it); then `q`, `p`, the division's quotient, remainder, divisor and
temporary, the remainders kept for `dP` and `dQ`, and `d`. -/

def aOne : Nat := 15
/-- Zero, for the check `n mod p = 0`. -/
def aZero : Nat := 10
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
  copy aDD aP, .block (bitOf sPodd aP), divL aDQ aDR aDD .s4, eqS sE1 aDQ aQ, eqS sE2 aDR aZero]

/-- `s8 := ⌈max(p_len, q_len) / 4⌉`, the primes' digits, without a branch:
`p_len - ((p_len - q_len) & mask)`, the mask all ones where `p_len < q_len`. -/
def nCalc : List Instr :=
  [.sltu .t6 .s4 .s6, .li .t5 0, .sub .t6 .t5 .t6, .sub .t5 .s4 .s6, .logic .and .t5 .t5 .t6,
    .sub .t5 .s4 .t5, .addi .t5 .t5 3, .shift .srl .d .s8 .t5 2]

/-- The inverse's start: `x = q`, `m = p | 1`, the primes' digits in `s8`, and
`[aOne] = 1`. -/
def invSetup : List (Prog isa) :=
  [copy InvBatch.aX aQ, copy InvBatch.aMin aP, .block (orOne InvBatch.aMin ++ nCalc), InvBatch.zeroW aOne,
    .block (setOne aOne)]

/-- The mask `0 - [sMask]` into `t4`. -/
def mask : List Instr := [.load .d .t4 .s11 sMask, .li .t5 0, .sub .t4 .t5 .t4]

/-- `qInv`, the gcd's check, the checks' mask and `qInv` written under it. -/
def invPart : Prog isa := seqs (invSetup ++ [
  InvBatch.inverse, eqS sE3 1 aOne,
  .block (andS sMask sPodd sE1 ++ andS sMask sMask sE2 ++ andS sMask sMask sE3 ++ mask),
  storeBytes 3 .a6 .s4])

/-- `d` divided by `p - 1` and by `q - 1`. -/
def dParts : Prog isa := seqs [
  copy aDQ aD, copy aDD aP, .block (clrLow aDD), divL aDQ aDR2 aDD .s4,
  copy aDQ aD, copy aDD aQ, .block (clrLow aDD), divL aDQ aDR3 aDD .s6]

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
