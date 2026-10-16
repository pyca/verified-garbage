module

public import VerifiedGarbage.Impl.Rsa.Arm.Inverse
public import VerifiedGarbage.Impl.Rsa.Arm.Div
public import VerifiedGarbage.Impl.Bignum.Arm.ModulusCheck
public import VerifiedGarbage.Impl.Bignum.Arm.LoadBE
public import VerifiedGarbage.Impl.Bignum.Arm.MaskBytes

/-! # `vg_rsa_crt_values` on ARMv7

`vg_rsa_crt_values(dp, dp_len, dq, dq_len, qinv, qinv_len, n, n_len, p,
p_len, q, q_len, d, d_len, scratch, scratch_len)`: the first four arguments
in `r0`–`r3`, the others on the stack. The function has no frame: it saves
the registers it must preserve, and its arguments, in the header of the
working space (`Impl/Rsa/Arm/KeyWs.lean`), and restores them from there.

`n` is checked as `vg_rsa_public_checked` checks it (it is public, and the
only branch on data). Then, with `w = ⌈n_len / 4⌉` words of 32 bits:

* `n`, `p`, `q` and `d` are read into arrays, and `n` divided by `p`
  (`Impl/Rsa/Arm/Div.lean`): `p q = n` is `p` odd, `n / p = q` and
  `n mod p = 0` (as `n` is odd).
* `qInv` is the inverse of `q` modulo `p | 1` (`Impl/Rsa/Arm/Inverse.lean`),
  which exists if the gcd it computes is 1.
* `dP` and `dQ` are `d` divided by `p` and by `q` with their low bits
  cleared: `p - 1` and `q - 1` for odd primes, which `p q = n` makes them.

The four checks are and'ed into a mask, under which the three results are
written out: zeros if any fails. A modulus that is not valid writes zeros
without any of this. Addresses and branches depend only on the pointers,
the lengths and `n`.
-/

@[expose] public section

namespace VG.Impl.Rsa.Arm.CrtValues
open VG VG.Arm VG.Impl.Bignum.Arm VG.Impl.Rsa.Arm.Keys

/-! ## The header

Bytes 0–19 are the division's; 20–52 hold `r4`–`r11` and `lr`, 56–96 the
arguments, 100–112 the slots of the shared routines and 116–132 the
checks. -/

def sDp : Nat := 56
def sDq : Nat := 60
def sQi : Nat := 64
def sN : Nat := 68
def sNl : Nat := 72
def sP : Nat := 76
def sPl : Nat := 80
def sQ : Nat := 84
def sQl : Nat := 88
def sD : Nat := 92
def sDl : Nat := 96
def sPodd : Nat := 116
def sE1 : Nat := 120
def sE2 : Nat := 124
def sE3 : Nat := 128
def sMask : Nat := 132

/-! ## The arrays

0–14 are `inverse`'s; then `1`, `q`, `p`, the division's quotient,
remainder, divisor and temporary, the remainders kept for `dP` and `dQ`, and
`d`. -/

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

/-- The working space's base into `r12`. -/
def entryBase : List Instr := [.ldrSp .r12 40]

/-- `r4`–`r11` and `lr`, and `dp` and `dq`, saved; the base into `r8` and
`dq` into `r3`. -/
def entrySave : List Instr :=
  [.str .r4 .r12 20, .str .r5 .r12 24, .str .r6 .r12 28, .str .r7 .r12 32, .str .r8 .r12 36,
   .str .r9 .r12 40, .str .r10 .r12 44, .str .r11 .r12 48, .str .lr .r12 52,
   .str .r0 .r12 sDp, .str .r2 .r12 sDq, .mov .r8 (.reg .r12), .mov .r3 (.reg .r2)]

/-- The stack arguments into registers: `qinv` (`r10`), `p_len` (`r11`),
`q_len` (`r12`), `n` (`r4`), `n_len` (`r6`), `p` (`r5`), `q` (`r7`), `d`
(`r9`) and `d_len` (`r1`). -/
def entryArgs : List Instr :=
  [.ldrSp .r10 0, .ldrSp .r11 20, .ldrSp .r12 28, .ldrSp .r4 8, .ldrSp .r6 12, .ldrSp .r5 16,
   .ldrSp .r7 24, .ldrSp .r9 32, .ldrSp .r1 36]

/-- The arguments saved, then `n` checked: Z if it is valid. -/
def entryCheck : List Instr :=
  [.str .r10 .r8 sQi, .str .r4 .r8 sN, .str .r6 .r8 sNl, .str .r5 .r8 sP, .str .r11 .r8 sPl,
   .str .r7 .r8 sQ, .str .r12 .r8 sQl, .str .r9 .r8 sD, .str .r1 .r8 sDl] ++ modulusCheck

def entry : List Instr := entryBase ++ entrySave ++ entryArgs ++ entryCheck

/-! ## An invalid modulus -/

/-- Zeros to `dp` (`r0`, `p_len` in `r11`), `dq` (`r3`, `q_len` in `r12`)
and `qinv` (`r10`), and 0 returned. -/
def fail : Prog isa := seqs [
  .block [.mov .r2 (.imm 0), .mov .lr (.reg .r11)], maskBytes,
  .block [.mov .r0 (.reg .r3), .mov .lr (.reg .r12)], maskBytes,
  .block [.mov .r0 (.reg .r10), .mov .lr (.reg .r11)], maskBytes,
  .block [.mov .r0 (.imm 0)]]

/-! ## A valid modulus -/

/-- `w = ⌈n_len / 4⌉` (`n_len` in `r6`) into `r9` and the header's
division count, the stride, and every array zeroed. -/
def setup : List Instr :=
  [.dp .add .r9 .r6 (.imm 3), .mov .r9 (.shifted .r9 .lsr 2)] ++ stride ++
  [.str .r9 .r8 16, .dp .add .r0 .r8 (.imm (BitVec.ofNat 32 hdr)), .mov .lr (.imm (BitVec.ofNat 32 nArr)),
   .mul .lr .lr .r7, .mov .lr (.shifted .lr .lsr 2), .mov .r3 (.imm 0)]

/-- The pointer and length in the slots `sPtr` and `sLen` into `r4` and `r6`. -/
def args (sPtr sLen : Nat) : List Instr := [.ldr .r4 .r8 sPtr, .ldr .r6 .r8 sLen]

/-- `[j] :=` the bytes at `r4` (`r6` of them). -/
def load (j : Nat) : Prog isa :=
  .seq (.block (ptr .r0 j ++ [.mov .r5 (.reg .r0), .dp .add .lr .r9 (.imm 2), .mov .r3 (.imm 0)])) loadBE

/-- The division's header: the arrays of quotient, remainder, divisor and temporary. -/
def divHdr (q r d t : Nat) : List Instr :=
  ptr .r1 q ++ [.str .r1 .r8 0] ++ ptr .r1 r ++ [.str .r1 .r8 4] ++
  ptr .r1 d ++ [.str .r1 .r8 8] ++ ptr .r1 t ++ [.str .r1 .r8 12]

/-- `w` back into `r9`, from the division's header. -/
def reload : List Instr := [.ldr .r9 .r8 16]

/-- `n`, `p`, `q` and `d` read, and `n` divided by `p`. -/
def loads : Prog isa := seqs [
  .block setup, zero, load aDQ,
  .block (args sP sPl), load aP,
  .block (args sQ sQl), load aQ,
  .block (args sD sDl), load aD]

/-- `p` odd, and the division of `n` by `p` set up. -/
def divN : List (Prog isa) := [
  copy aDD aP, .block (bitOf sPodd aP ++ divHdr aDQ aDR aDD aDT)]

/-- `inverse`'s start: `(u, v, x₁, x₂) = (q, m, 1, 0)` with `m = p | 1`,
`[aNM] = 2^(32 w) - m` and `[aOne] = 1`. -/
def invSetup : List (Prog isa) := [
  copy 0 aQ, copy aM aP, .block (orOne aM), copy 1 aM, .block (setOne 2 ++ setOne aOne),
  sub3 aNM aZero aM]

/-- The checks of `p q = n` and of the inverse, `qInv` computed, and the
division of `d` by `p - 1` set up. -/
def checks : Prog isa := seqs ([
  .block stride, eqS sE1 aDQ aQ aT1, eqS sE2 aDR aZero aT1] ++ invSetup ++ [
  inverse, eqS sE3 1 aOne aT1,
  .block (andS sMask sPodd sE1 ++ andS sMask sMask sE2 ++ andS sMask sMask sE3),
  copy aDQ aD, copy aDD aP, .block (clrLow aDD ++ divHdr aDQ aDR2 aDD aDT)])

/-- The division of `d` by `q - 1` set up. -/
def divQ : Prog isa := seqs [
  .block stride, copy aDQ aD, copy aDD aQ, .block (clrLow aDD ++ divHdr aDQ aDR3 aDD aDT)]

/-- The pointer and length in the slots `sPtr` and `sLen` into `r10` and `r11`. -/
def outArgs (sPtr sLen : Nat) : List Instr := [.ldr .r10 .r8 sPtr, .ldr .r11 .r8 sLen]

/-- `[j]`'s low `r11` bytes to `r10`, most significant first, masked by the
slot `sMask`. -/
def store (j : Nat) : Prog isa := seqs [
  .block (ptr .r1 j ++ [.dp .add .r1 .r1 (.reg .r11), .dp .sub .r1 .r1 (.imm 1), .mov .r0 (.reg .r10),
    .mov .lr (.reg .r11)]),
  reverseBytes,
  .block [.mov .r0 (.reg .r10), .mov .lr (.reg .r11), .ldr .r1 .r8 sMask, .mov .r2 (.imm 0),
    .dp .sub .r2 .r2 (.reg .r1)],
  maskBytes]

def valid : Prog isa := seqs [
  loads, seqs divN, Rsa.Arm.Div.code, .block reload, checks, Rsa.Arm.Div.code, .block reload,
  divQ, Rsa.Arm.Div.code, .block reload, .block stride,
  .block (outArgs sDp sPl), store aDR2,
  .block (outArgs sDq sQl), store aDR3,
  .block (outArgs sQi sPl), store 3,
  .block [.ldr .r0 .r8 sMask]]

/-- `r4`–`r11` and `lr` restored, the base last. -/
def restore : List Instr :=
  [.ldr .r4 .r8 20, .ldr .r5 .r8 24, .ldr .r6 .r8 28, .ldr .r7 .r8 32, .ldr .r9 .r8 40,
   .ldr .r10 .r8 44, .ldr .r11 .r8 48, .ldr .lr .r8 52, .ldr .r8 .r8 36]

/-- `vg_rsa_crt_values`. -/
def code : Prog isa := .seq (.block entry) (.seq (.ite .eq valid fail) (.block restore))

end VG.Impl.Rsa.Arm.CrtValues
