module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.Div
public import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyArrays
public import VerifiedGarbage.Impl.Rsa.PPC64LE.InvBatch
public import VerifiedGarbage.Impl.Rsa.PPC64LE.MontKey
public import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyDiv

/-!
# `vg_rsa_crt_values` on PPC64LE

`vg_rsa_crt_values(dp, dp_len, dq, dq_len, qinv, qinv_len, n, n_len, p,
p_len, q, q_len, d, d_len, scratch, scratch_len)`: the first eight arguments
in `r3`–`r10`, the others on the stack, at `sp + 96 + 8 i` for the `i`-th of
them (`p` is the 0th). As on ARMv7 (`Impl/Rsa/Arm/CrtValues.lean`):

`n` is checked as `vg_rsa_public_precompute` checks it (it is public, and the
only branch on data). Then, with `w = 2 ⌈n_len / 8⌉` digits of 32 bits (even,
so that the inverse's `⌈n / 2⌉ + 1` words fit in an array of `w + 2` digits):

* `n`, `p`, `q` and `d` are read into arrays: `p q = n` is `p` odd,
  `p q ≡ n (mod 2^(32 w))` (`MontKey.mulLo`) and `n ≡ 0 (mod p)`, as
  Montgomery's `n 2^(-32 w) mod (p | 1)` (`MontKey.montMul`) is 0
  (`Proof/Rsa/MontCheckMath.lean`'s `pq_eq_iff`).
* `qInv` is the inverse of `q` modulo `p | 1` (`InvBatch.lean`), which exists
  if the gcd it computes is 1, at the primes' width: `⌈max(p_len, q_len) / 4⌉`
  digits.
* `dP` and `dQ` are the remainders of `d` divided by `p` and by `q` with
  their low bits cleared: `p - 1` and `q - 1` for odd primes, which `p q = n`
  makes them. For a balanced key of full words (`shape`, from the lengths
  alone) by words (`KeyDiv.divW`), exact when the divisor's top word is not
  zero, as it is when `p q = n`; otherwise bit-serial (`Div.divP`).

The four checks are and'ed into a mask, under which the three results are
written out: zeros if any fails. A modulus that is not valid writes zeros
without any of this. Addresses and branches depend only on the pointers,
the lengths and `n`.

The pointers and lengths stay in the nonvolatile `r14`–`r24` throughout
(`dp`, `dq`, `qinv`, `n`, `n_len`, `p`, `p_len`, `q`, `q_len`, `d`,
`d_len`), so no address or count is ever loaded from memory. They and the
nonvolatile `r29`–`r31` the shared routines use are saved in the header of
the working space.
-/

@[expose] public section

namespace VG.Impl.Rsa.PPC64LE.CrtValues

open VG.PPC64LE VG.Impl.Rsa.PPC64LE.Keys VG.Impl.Rsa.PPC64LE.Div

/-! ## The header

Bytes 0–111 hold `r14`–`r24` and `r29`–`r31`, 124–132 the shared routines'
slots and 136–152 the checks. -/

def sPodd : Nat := 136
def sE1 : Nat := 140
def sE2 : Nat := 144
def sE3 : Nat := 148
def sMask : Nat := 152

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

/-! ## The stack arguments -/

/-- The offset from the stack pointer of the `i`-th stack argument. -/
def stackOff (i : Nat) : Nat := 96 + 8 * i

/-- The `i`-th stack argument into `r`. -/
def stackArg (r : Reg) (i : Nat) : List Instr := [.addSp r (stackOff i), .load .d r r 0]

/-! ## Entry -/

/-- The working space's base into `r11`, the registers saved there, the
base into `r31`, and the pointers and lengths into `r14`–`r24`. -/
def entry : List Instr :=
  stackArg .r11 6 ++
  [.store .d .r14 .r11 0, .store .d .r15 .r11 8, .store .d .r16 .r11 16, .store .d .r17 .r11 24,
    .store .d .r18 .r11 32, .store .d .r19 .r11 40, .store .d .r20 .r11 48, .store .d .r21 .r11 56,
    .store .d .r22 .r11 64, .store .d .r23 .r11 72, .store .d .r24 .r11 80, .store .d .r29 .r11 88,
    .store .d .r30 .r11 96, .store .d .r31 .r11 104, .addi .r31 .r11 0,
    .addi .r14 .r3 0, .addi .r15 .r5 0, .addi .r16 .r7 0, .addi .r17 .r9 0, .addi .r18 .r10 0] ++
  stackArg .r19 0 ++ stackArg .r20 1 ++ stackArg .r21 2 ++ stackArg .r22 3 ++ stackArg .r23 4 ++
  stackArg .r24 5

/-- `n`'s last byte's low bit, inverted, into `r0`, and its first byte into
`r11`. -/
def check1 : List Instr :=
  [.add .r11 .r9 .r10, .subi .r11 .r11 1, .lbz .r0 .r11 0, .li .r12 1,
    .logic .and .r0 .r0 .r12, .logic .xor .r0 .r0 .r12, .lbz .r11 .r9 0]

/-- The rest of `check`, from the bytes `check1` loaded. -/
def check2 : Prog isa :=
  .seq (.ite (.zero .d .r11) (.block [.li .r0 1]) (.block []))
    (.seq (.block [.subi .r12 .r10 64])
      (.ite (.zero .d .r12) (.block [.lsr .d .r11 .r11 7, .li .r12 1, .logic .xor .r11 .r11 .r12,
        .logic .or .r0 .r0 .r11]) (.block [])))

/-- Whether `n` (`r9`, `n_len` bytes in `r10`) is a valid modulus, in `r0`:
0 if it is. Its last byte is odd, its first is not zero, and if `n_len = 64`,
its first byte's top bit is set. -/
def check : Prog isa := .seq (.block check1) check2

/-! ## An invalid modulus -/

/-- `r8` zero bytes from `r5`. -/
def zeroBytes : Prog isa :=
  .seq (.block [.li .r0 0]) (countLoop .r8 [.stb .r0 .r5 0, .addi .r5 .r5 1])

/-- Zeros to `dp`, `dq` and `qinv`, and 0 returned. -/
def fail : Prog isa := seqs [
  .block [.addi .r5 .r14 0, .addi .r8 .r20 0], zeroBytes,
  .block [.addi .r5 .r15 0, .addi .r8 .r22 0], zeroBytes,
  .block [.addi .r5 .r16 0, .addi .r8 .r20 0], zeroBytes,
  .block [.li .r3 0]]

/-! ## A valid modulus -/

/-- `w = 2 ⌈n_len / 8⌉` into `r29`, the stride into `r30`, and every array
zeroed. -/
def setup : Prog isa :=
  .seq (.block ([.addi .r29 .r18 7, .lsr .d .r29 .r29 3, .lsl .r29 .r29 1] ++ stride ++
      [.li .r8 nArr, .mul .r8 .r8 .r30, .lsr .d .r8 .r8 2]))
    (zeroArrays .r8)

/-- `[j] :=` the `r8` bytes at `r6`, most significant first: byte `i` is byte
`r8 - 1 - i` of the number, which is little-endian in memory. -/
def load (j : Nat) : Prog isa :=
  .seq (.block (ptr .r5 j ++ [.add .r5 .r5 .r8, .subi .r5 .r5 1]))
    (countLoop .r8 [.lbz .r0 .r6 0, .stb .r0 .r5 0, .addi .r6 .r6 1, .subi .r5 .r5 1])

/-- `n`, `p`, `q` and `d` read. -/
def loads : Prog isa := seqs [
  .block [.addi .r6 .r17 0, .addi .r8 .r18 0], load aDQ,
  .block [.addi .r6 .r19 0, .addi .r8 .r20 0], load aP,
  .block [.addi .r6 .r21 0, .addi .r8 .r22 0], load aQ,
  .block [.addi .r6 .r23 0, .addi .r8 .r24 0], load aD]

/-- `r11 := ⌈max(p_len, q_len) / 4⌉`, the primes' digits, without a branch:
`p_len - ((p_len - q_len) & mask)`, the mask all ones where `p_len < q_len`. -/
def nCalc : List Instr :=
  [.sub .r11 .r20 .r22, .lsr .d .r0 .r11 63, .li .r3 0, .sub .r0 .r3 .r0, .logic .and .r11 .r11 .r0,
    .sub .r11 .r20 .r11, .addi .r11 .r11 3, .lsr .d .r11 .r11 2]

/-- The inverse's start: `x = q`, `m = p | 1`, `[aOne] = 1` and the primes'
digits in `r11`. -/
def invSetup : List (Prog isa) := [copy 0 aQ, copy aM aP, .block (orOne aM ++ setOne aOne ++ nCalc)]

/-- `r0 := 0` exactly for a balanced key of full words: `p_len` (`r20`) a
multiple of 8 and at least 32, equal to `q_len` (`r22`) and to `2 w`
(`r29`). -/
def shape : List Instr :=
  [.li .r0 7, .logic .and .r0 .r20 .r0, .lsl .r3 .r29 1, .logic .xor .r3 .r3 .r20, .logic .or .r0 .r0 .r3,
    .logic .xor .r3 .r20 .r22, .logic .or .r0 .r0 .r3, .lsr .d .r3 .r20 5, .li .r12 0, .sub .r3 .r12 .r3,
    .lsr .d .r3 .r3 63, .li .r12 1, .logic .xor .r3 .r3 .r12, .logic .or .r0 .r0 .r3]

/-- For `K = 5 (3 ν + 2) = 64 Q + T` (`ν = w / 4`, the inverse's words for a
balanced key): `r6 :=` `y`'s address (array 3), `r5 :=` that of word `Q` of
`aDR`, `r7 := T`, `r8 := ν + 1`, `r9 := 0` and `r12 := 1`. -/
def tailSetup : List Instr :=
  ptr .r6 InvBatch.aY ++ ptr .r5 aDR ++
  [.lsr .d .r3 .r29 2, .lsl .r4 .r3 4, .sub .r4 .r4 .r3, .addi .r4 .r4 10, .li .r0 63, .logic .and .r7 .r4 .r0,
    .lsr .d .r4 .r4 6, .lsl .r4 .r4 3, .add .r5 .r5 .r4, .addi .r8 .r3 1, .li .r9 0, .li .r12 1]

/-- `r12 := 2^T`, by `T` (`r7`) doublings. -/
def pow2T : Prog isa := .ite (.zero .d .r7) (.block []) (countLoop .r7 [.add .r12 .r12 .r12])

/-- One word of `y 2^T` (`2^T` in `r12`): the word at `r6` times `2^T`, its low
word with the carry `r9` in to `r5`, its high word the carry out. -/
def shlBody : List Instr :=
  [.load .d .r0 .r6 0, .mulhu .r3 .r0 .r12, .mul .r0 .r0 .r12, .logic .or .r0 .r0 .r9, .store .d .r0 .r5 0,
    .addi .r9 .r3 0, .addi .r5 .r5 8, .addi .r6 .r6 8]

/-- `y := y 2^K mod p`, for `y < p` of `ν` words in array 3: `y 2^K`, `y`'s
`ν + 1` words times `2^T` into the zeroed `aDR` at word `Q`, divided by `p`
(array 8, copied to array 4 with its top word made not zero) into the zeroed
array 3, through array 5 and the save area `aDQ` (`KeyDiv.divW`). -/
def tail : Prog isa := seqs [InvBatch.zeroW aDR, .block tailSetup, pow2T, countLoop .r8 shlBody,
  InvBatch.zeroW InvBatch.aY, copy InvBatch.aF InvBatch.aMin, .block (KeyDiv.fixTop InvBatch.aF),
  KeyDiv.divW aDR InvBatch.aY InvBatch.aF InvBatch.aG aDQ]

/-- `d` divided by `[a]` (`p` or `q`) with its low bit cleared, by words, the
remainder in `[r]`: `[a]` copied to `aDD`, its top word made not zero
(`KeyDiv.fixTop`), `aDQ` the save area (`KeyDiv.divW`). -/
def divW (a r : Nat) : List (Prog isa) :=
  [copy aDD a, .block (clrLow aDD), .block (KeyDiv.fixTop aDD), KeyDiv.divW aD r aDD aDT aDQ]

/-- The same, bit-serial, `[a]`'s length in bytes in `len`. -/
def divB (len : Reg) (a r : Nat) : List (Prog isa) :=
  [copy aDQ aD, copy aDD a, .block (clrLow aDD ++ [.addi .r12 len 0]), divP aDQ r aDD aDT]

/-- `p` odd, `p q mod 2^(32 w)` compared with `n`, Montgomery's `n` modulo
`p | 1` (with 1 in `aDR3`) compared with 0, the check of the inverse, `qInv`
computed, and `d` divided by `p - 1` and by `q - 1`: by words for a balanced
key (`shape`, both divisions on one branch), else bit-serial. -/
def arith : Prog isa := seqs ([
  .block (bitOf sPodd aP), MontKey.mulLo aDR aP aQ .r20, eqS sE1 aDR aDQ, copy aDD aP,
  .block (orOne aDD ++ setOne aDR3), MontKey.montMul aDT aDQ aDR3 aDD aDR2 .r20 MontKey.cntW,
  eqS sE2 aDT aZero] ++ invSetup ++ [
  .block shape, .ite (.zero .d .r0) InvBatch.inverseS InvBatch.inverse, eqS sE3 1 aOne,
  .block (andS sMask sPodd sE1 ++ andS sMask sMask sE2 ++ andS sMask sMask sE3),
  .block shape, .ite (.zero .d .r0) (seqs (tail :: (divW aP aDR2 ++ divW aQ aDR3)))
    (seqs (divB .r20 aP aDR2 ++ divB .r22 aQ aDR3))])

/-- `[j]`'s low `r8` bytes to `r5`, most significant first, masked by `r9`. -/
def storeBytes (j : Nat) : Prog isa :=
  .seq (.block (ptr .r6 j ++ [.add .r6 .r6 .r8, .subi .r6 .r6 1]))
    (countLoop .r8 [.lbz .r0 .r6 0, .logic .and .r0 .r0 .r9, .stb .r0 .r5 0, .addi .r5 .r5 1,
      .subi .r6 .r6 1])

/-- The mask `0 - [sMask]` into `r9`. -/
def mask : List Instr := [.load .w .r9 .r31 sMask, .li .r0 0, .sub .r9 .r0 .r9]

/-- The three results written out under the mask, and the mask's bit returned. -/
def stores : Prog isa := seqs [
  .block ([.addi .r5 .r14 0, .addi .r8 .r20 0] ++ mask), storeBytes aDR2,
  .block ([.addi .r5 .r15 0, .addi .r8 .r22 0] ++ mask), storeBytes aDR3,
  .block ([.addi .r5 .r16 0, .addi .r8 .r20 0] ++ mask), storeBytes 3,
  .block [.load .w .r3 .r31 sMask]]

def valid : Prog isa := seqs [setup, loads, arith, stores]

/-- The saved registers restored, `r31` last. -/
def restore : List Instr :=
  [.load .d .r14 .r31 0, .load .d .r15 .r31 8, .load .d .r16 .r31 16, .load .d .r17 .r31 24,
    .load .d .r18 .r31 32, .load .d .r19 .r31 40, .load .d .r20 .r31 48, .load .d .r21 .r31 56,
    .load .d .r22 .r31 64, .load .d .r23 .r31 72, .load .d .r24 .r31 80, .load .d .r29 .r31 88,
    .load .d .r30 .r31 96, .load .d .r31 .r31 104]

/-- `vg_rsa_crt_values`. -/
def code : Prog isa :=
  .seq (.block entry) (.seq check (.seq (.ite (.zero .d .r0) valid fail) (.block restore)))

end VG.Impl.Rsa.PPC64LE.CrtValues
