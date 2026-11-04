module

public import VerifiedGarbage.Impl.RsaOaep.RISCV64
public import VerifiedGarbage.Impl.Rsa.RISCV64.Priv

/-!
# RSAES-OAEP decryption (RFC 8017 §7.1.2) on RISC-V

`vg_rsa_oaep_<H>_mgf1_decrypt(out = a0, out_len = a1, msg_len = a2, n = a3,
n_len = a4, e = a5, e_len = a6, p = a7, p_len, q, q_len, dp, dp_len, dq,
dq_len, qinv, qinv_len, label, label_len, ct, ct_len, scratch, scratch_len,
mgf1)`, the last sixteen on the stack, for a hash function `H` (the label's),
an `Impl.Hmac.Stream.RISCV64.Hash` (its streaming functions), and MGF1 over
the hash function of the table `mgf1` of the interface `Hash`, which it
calls, with `vg_rsa_private_checked`.
The steps are those of PPC64LE (`Impl/RsaOaep/PPC64LE/Decrypt.lean`).

It runs in the frame of encryption (`Impl/RsaOaep/RISCV64.lean`, `save` and
`restore`), with the same part of `scratch` and its MGF1 (`mgfXorT`,
`seedArgs`, `dbArgs`). The values the code keeps across the calls are in
`s0`–`s4`: `s0` = `scratch`, `s1` = `k = n_len`, `s2` = `out`, `s3` =
`msg_len`, and, after the private operation, `s4` its result `r` (1, 0 or
2), zero-extended from the 32 bits the calling convention gives it. The
label and its length are read from our stack arguments when they are hashed,
after MGF1 has used `s6`–`s11`.

`vg_rsa_private_checked` takes twelve arguments on the stack: it is called
from a frame of its own of `privBytes` bytes below ours, which holds them,
and writes `EM` (or zeros) to `EM`'s place in `scratch`, with the rest of
`scratch` from `oRsa` as its working space. Its result only selects values
without a branch. If `k < 2 hLen + 2` (public), the result is
`r = 2 ? 2 : 0`, with zeros to `out` and `*msg_len`. Otherwise, without a
branch on anything secret: the seed and `DB` are unmasked in place (`G`),
and the label is hashed (`H`) to `scratch + oDig`; an accumulator `acc`
(`s5`) ORs together `EM`'s first byte and `lHash' ⊕ lHash`; the scan over
`T = DB[hLen..]` (`t = k - 2 hLen - 1` bytes) finds the index `idx` (`s6`)
of its first `0x01` with masks, and ORs into `acc` a mask if a byte before
it is neither zero nor `0x01`, or if there is none; `T` is copied into the
2048-byte buffer `scratch + oBuf`, zeros after it, and shifted left by
`idx + 1` bytes in ten passes, pass `j` replacing each of its first `k`
bytes by the one `2^j` bytes after it under the mask of bit `j` of
`idx + 1`: the message, then zeros. With `ok` (`s7`) all ones exactly when
`r = 1` and `acc = 0`, `out` receives the buffer's first `k` bytes ANDed
with `ok`, `*msg_len` receives `(t - idx - 1) ∧ ok`, and the result is
`(ok ∧ 1) ∨ (r = 2 ? 2 : 0)`.

The buffer is past the reach of an immediate and so addressed from
`scratch + oBuf` (`bufBase`). A comparison `a < b` of values below `2⁶³` is
the top bit of `a - b`, and `x ≠ 0` is the top bit of `x ∨ -x`. Every
branch and address depends only on the pointers and the lengths.
-/

@[expose] public section

namespace VG.Impl.RsaOaep.RISCV64.Dec

open VG VG.RISCV64
open VG.Impl.Hmac.Stream.RISCV64 (Hash mov)
open VG.Impl.Bignum.RISCV64 (countLoop)
open VG.Impl.RsaPkcs1Sig.RISCV64 (copyLoop fillLoop)
open VG.Impl.RsaOaep.RISCV64 (frameBytes argBase save restore zeroOut oEm oSt oDig oRsa mgfXorT seedArgs dbArgs Fns
  chkK)

/-! ## More of our part of `scratch` -/

/-- The buffer in which `T` is shifted: 2048 bytes. -/
def oBuf : Nat := 2560

/-- `d := scratch + oBuf`. -/
def bufBase (d : Reg) : List Instr := [.addi d .s0 2047, .addi d d 513]

/-! ## The entry -/

/-- The arguments into the registers that keep them: `scratch` (our stack
argument 13), `k`, `out` and `msg_len`. -/
def prologue : List Instr := [argBase, .load .d .s0 .t6 104, mov .s1 .a4, mov .s2 .a0, mov .s3 .a2]

/-! ## The private operation -/

/-- The frame from which `vg_rsa_private_checked` is called: its twelve
stack arguments, at its `sp`. -/
def privBytes : Nat := 96

/-- `vg_rsa_private_checked`. -/
def privCall : Prog isa := .call "vg_rsa_private_checked" Impl.Rsa.RISCV64.Priv.code

/-- Our stack argument `j` (`p_len` … `qinv_len`) to its stack argument
`j + 1`. -/
def copyArg (j : Nat) : List Instr := [.load .d .t1 .t6 (8 * j), .store .d .t1 .t0 (8 * (j + 1))]

/-- Its arguments, with `t0` its `sp` and `t6` our first stack argument: on
the stack `p` (`a7`) and our stack arguments 0 to 8, then the rest of
`scratch` from `oRsa` and `scratch_len - 1024`; in the registers `EM`'s
place (`k` bytes), `n`, `e` and the ciphertext (`k` bytes). -/
def privArgs : List Instr :=
  [.addSp .t0 0, .addSp .t6 (privBytes + frameBytes), .store .d .a7 .t0 0] ++ (List.range 9).flatMap copyArg ++
    [.li .t1 1024, .shift .sll .d .t1 .t1 3, .add .t1 .s0 .t1, .store .d .t1 .t0 80, .load .d .t1 .t6 112,
      .addi .t1 .t1 (-1024), .store .d .t1 .t0 88, mov .a2 .a3, mov .a3 .s1, mov .a4 .a5, mov .a5 .a6,
      .load .d .a6 .t6 88, mov .a7 .s1, .addi .a0 .s0 oEm, mov .a1 .s1]

/-- The private operation, from its frame; its result into `s4`,
zero-extended. -/
def priv : Prog isa :=
  .seq (.frame (.alloc privBytes) (.seq (.block privArgs) privCall) (.free privBytes))
    (.block [.shift .sll .d .s4 .a0 32, .shift .srl .d .s4 .s4 32])

/-! ## Failing -/

/-- `a0 := (r = 2) ? 2 : 0`, for `r < 2⁶³`. -/
def faultBit : List Instr :=
  [.li .a1 2, .logic .xor .a0 .s4 .a1, .addi .a0 .a0 (-1), .shift .srl .d .a0 .a0 63, .add .a0 .a0 .a0]

/-- Zeros to `out` and `*msg_len`, and the result `(r = 2) ? 2 : 0`. -/
def decFail : Prog isa := .seq zeroOut (.block ([.li .t1 0, .store .d .t1 .s3 0] ++ faultBit))

variable (H : Hash)

/-! ## The decoding -/

/-- `H(label)` to `scratch + oDig`, the label and its length from our
stack arguments 9 and 10. -/
def hashLabel : Prog isa :=
  .seq (.block [.addi .a0 .s0 oSt]) (.seq H.callInit
  (.seq (.block [argBase, .addi .a0 .s0 oSt, .li .a1 0, .load .d .a2 .t6 72, .load .d .a3 .t6 80])
  (.seq H.callUpd
  (.seq (.block [argBase, .addi .a0 .s0 oSt, .load .d .a1 .t6 80, .addi .a2 .s0 oDig]) H.callFin))))

/-- A byte of `lHash'` XORed with `lHash`'s, ORed into `acc`. -/
def accBody : List Instr :=
  [.load .b .t1 .a4 0, .load .b .t2 .a5 0, .logic .xor .t1 .t1 .t2, .logic .or .s5 .s5 .t1, .addi .a4 .a4 1,
    .addi .a5 .a5 1]

/-- `acc := EM[0] ∨ ⋁ (lHash'[i] ⊕ lHash[i])`, in `s5`. -/
def accLh : Prog isa :=
  .seq (.block [.addi .a4 .s0 ((oEm + 1 + H.D : Nat) : Int), .addi .a5 .s0 oDig, .load .b .s5 .s0 oEm,
    .li .a6 H.D]) (countLoop .a6 accBody)

/-- `T`'s address in `a1` and its length `t = k - 2 hLen - 1` in `a2`. -/
def tArgs : List Instr := [.addi .a1 .s0 ((oEm + 1 + 2 * H.D : Nat) : Int), .addi .a2 .s1 (-(2 * H.D + 1 : Nat))]

/-- A byte `b` of `T` (at `a1`, its index in `a3`): with `z = (b = 0)` and
`o = (b = 1)`, `acc ∨= looking ∧ ((z ∨ o) - 1)`, `idx ∨= i ∧ looking ∧ -o`,
`looking ∧= o - 1`; `looking` (`a4`) is all ones while no `0x01` has been
seen. -/
def scanBody : List Instr :=
  [.load .b .a7 .a1 0, .addi .t1 .a7 (-1), .shift .srl .d .t1 .t1 63, .li .t2 1, .logic .xor .t2 .a7 .t2,
    .addi .t2 .t2 (-1), .shift .srl .d .t2 .t2 63, .logic .or .t1 .t1 .t2, .addi .t1 .t1 (-1),
    .logic .and .t1 .t1 .a4, .logic .or .s5 .s5 .t1, .li .t3 0, .sub .t3 .t3 .t2, .logic .and .t1 .a3 .a4,
    .logic .and .t1 .t1 .t3, .logic .or .s6 .s6 .t1, .addi .t2 .t2 (-1), .logic .and .a4 .a4 .t2,
    .addi .a1 .a1 1, .addi .a3 .a3 1]

/-- The scan of `T`, then `acc ∨= looking`. -/
def scan : Prog isa :=
  .seq (.block (tArgs H ++ [.li .a3 0, .li .a4 0, .addi .a4 .a4 (-1), .li .s6 0]))
    (.seq (countLoop .a2 (scanBody)) (.block [.logic .or .s5 .s5 .a4]))

/-- The buffer's 2048 bytes cleared (`2048 = 1 << 11`, past the reach of an
immediate). -/
def clearBuf : Prog isa := .seq (.block (bufBase .a1 ++ [.li .t5 1, .shift .sll .d .t5 .t5 11, .li .t0 0])) fillLoop

/-- `T` to the buffer. -/
def copyT : Prog isa :=
  .seq (.block ([.addi .a4 .s0 ((oEm + 1 + 2 * H.D : Nat) : Int)] ++ bufBase .a1 ++
    [.addi .a5 .s1 (-(2 * H.D + 1 : Nat))])) copyLoop

/-- A byte of the buffer replaced by the one `d` bytes after it under the
mask `a3`. -/
def passBody : List Instr :=
  [.load .b .t1 .a1 0, .load .b .t2 .a2 0, .logic .xor .t2 .t2 .t1, .logic .and .t2 .t2 .a3,
    .logic .xor .t1 .t1 .t2, .store .b .t1 .a1 0, .addi .a1 .a1 1, .addi .a2 .a2 1]

/-- A pass: each of the buffer's first `k` bytes replaced by the one `d`
(`s9`) bytes after it if bit 0 of `a` (`s8`) is set. -/
def shiftPass : Prog isa :=
  .seq (.block (bufBase .a1 ++ [.add .a2 .a1 .s9, .li .a3 1, .logic .and .a3 .s8 .a3, .li .a4 0,
      .sub .a3 .a4 .a3, mov .a5 .s1]))
    (countLoop .a5 passBody)

/-- The buffer shifted left by `idx + 1` (`a`, from `s6`) bytes, in ten
passes (`s10`), the `j`-th by `d = 2^j` (`s9`). -/
def shift : Prog isa :=
  .seq (.block [.addi .s8 .s6 1, .li .s9 1, .li .s10 10])
    (.loop (.seq shiftPass (.block [.shift .srl .d .s8 .s8 1, .add .s9 .s9 .s9, .addi .s10 .s10 (-1)]))
      (.nonzero .s10))

/-- `ok` (`s7`): all ones iff `r = 1` and `acc = 0`. -/
def okMask : List Instr :=
  [.li .a1 1, .logic .xor .a1 .s4 .a1, .addi .a1 .a1 (-1), .shift .srl .d .a1 .a1 63, .li .a2 0,
    .sub .a2 .a2 .s5, .logic .or .a2 .a2 .s5, .shift .srl .d .a2 .a2 63, .li .a3 1, .logic .xor .a2 .a2 .a3,
    .logic .and .a1 .a1 .a2, .li .s7 0, .sub .s7 .s7 .a1]

/-- A byte of the buffer, ANDed with `ok`, to `out`. -/
def outBody : List Instr :=
  [.load .b .t1 .a4 0, .logic .and .t1 .t1 .s7, .store .b .t1 .a5 0, .addi .a4 .a4 1, .addi .a5 .a5 1]

/-- The buffer's first `k` bytes, ANDed with `ok`, to `out`. -/
def outLoop : Prog isa := .seq (.block (bufBase .a4 ++ [mov .a5 .s2, mov .a6 .s1])) (countLoop .a6 outBody)

/-- `*msg_len := (t - idx - 1) ∧ ok`, and the result
`(ok ∧ 1) ∨ ((r = 2) ? 2 : 0)`. -/
def decRet : List Instr :=
  [.addi .a1 .s1 (-(2 * H.D + 2 : Nat)), .sub .a1 .a1 .s6, .logic .and .a1 .a1 .s7, .store .d .a1 .s3 0] ++
    faultBit ++ [.li .a1 1, .logic .and .a1 .s7 .a1, .logic .or .a0 .a0 .a1]

variable (f : Fns)

/-- After the private operation and the check of `k`: the decoding, with
MGF1's hash function the table that is our stack argument 15. -/
def decMain : Prog isa :=
  .seq (.block (seedArgs H)) (.seq (mgfXorT f 15) (.seq (.block (dbArgs H)) (.seq (mgfXorT f 15) (.seq (hashLabel H)
  (.seq (accLh H) (.seq (scan H) (.seq clearBuf (.seq (copyT H) (.seq shift (.seq (.block okMask) (.seq outLoop
  (.block (decRet H)))))))))))))

/-! ## The function -/

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block (save ++ prologue)) (.seq priv (.seq (.block (chkK H))
    (.seq (.ite (.nonzero .a0) decFail (decMain H f)) (.block restore))))

/-- `vg_rsa_oaep_<H>_mgf1_decrypt`, with MGF1's hash function the table that
is its stack argument 15 (`mgf1`). -/
def decrypt : Prog isa := .frame (.alloc frameBytes) (body H f) (.free frameBytes)

end VG.Impl.RsaOaep.RISCV64.Dec
