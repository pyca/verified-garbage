module

public import VerifiedGarbage.Impl.RsaOaep.PPC64LE
public import VerifiedGarbage.Impl.Rsa.PPC64LE.Priv

/-!
# RSAES-OAEP decryption (RFC 8017 §7.1.2) on PPC64LE

`vg_rsa_oaep_<H>_mgf1_<G>_decrypt(out = r3, out_len = r4, msg_len = r5,
n = r6, n_len = r7, e = r8, e_len = r9, p = r10, p_len, q, q_len, dp,
dp_len, dq, dq_len, qinv, qinv_len, label, label_len, ct, ct_len, scratch,
scratch_len)`, the last fifteen on the stack, for a hash function `H` (the
label's) and MGF1's hash function `G`, each an `Impl.Hmac.Stream.PPC64LE.Hash`
(its streaming functions), which it calls, with `vg_rsa_private_checked`.
The steps are those of AArch64 (`Impl/RsaOaep/AArch64.lean`).

It runs in the frame of encryption (`Impl/RsaOaep/PPC64LE.lean`, `save` and
`restore`), with the same part of `scratch` and its MGF1 (`mgfXor`,
`seedArgs`, `dbArgs`). The values the code keeps across the calls are in
`r14`–`r20`: `r14` = `scratch`, `r15` = `k = n_len`, `r16` = `out`, `r17` =
`msg_len`, `r18` = `label`, `r19` = `label_len`, and, after the private
operation, `r20` its result `r` (1, 0 or 2), zero-extended from the 32 bits
the calling convention gives it.

`vg_rsa_private_checked` takes twelve arguments on the stack, which the
Parameter Save Area of our frame cannot hold below the saved registers: it
is called from a frame of its own of `privBytes` bytes, whose Parameter Save
Area holds them, and writes `EM` (or zeros) to `EM`'s place in `scratch`,
with the rest of `scratch` from `oRsa` as its working space. Its result only
selects values without a branch. If `k < 2 hLen + 2` (public), the result is
`r = 2 ? 2 : 0`, with zeros to `out` and `*msg_len`. Otherwise, without a
branch on anything secret: the seed and `DB` are unmasked in place (`G`),
and the label is hashed (`H`) to `scratch + oDig`; an accumulator `acc` (`r24`) ORs
together `EM`'s first byte and `lHash' ⊕ lHash`; the scan over
`T = DB[hLen..]` (`t = k - 2 hLen - 1` bytes) finds the index `idx` (`r25`)
of its first `0x01` with masks, and ORs into `acc` a mask if a byte before
it is neither zero nor `0x01`, or if there is none; `T` is copied into the
2048-byte buffer `scratch + oBuf`, zeros after it, and shifted left by
`idx + 1` bytes in ten passes, pass `j` replacing each of its first `k`
bytes by the one `2^j` bytes after it under the mask of bit `j` of
`idx + 1`: the message, then zeros. With `ok` all ones exactly when `r = 1`
and `acc = 0`, `out` receives the buffer's first `k` bytes ANDed with `ok`,
`*msg_len` receives `(t - idx - 1) ∧ ok`, and the result is
`(ok ∧ 1) ∨ (r = 2 ? 2 : 0)`.

A comparison `a < b` of values below `2⁶³` is the top bit of `a - b`, and
`x ≠ 0` is the top bit of `x ∨ -x`. Every branch and address depends only on
the pointers and the lengths.
-/

@[expose] public section

namespace VG.Impl.RsaOaep.PPC64LE.Dec

open VG VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov)
open VG.Impl.Hmac.Stream.PPC64LE (Hash)
open VG.Impl.RsaOaep.PPC64LE (frameBytes arg save restore copyLoop zeroLoop zeroOut oEm oSt oDig oW oRsa mgfXor
  seedArgs dbArgs)

/-! ## More of our part of `scratch` -/

/-- The buffer in which `T` is shifted: 2048 bytes. -/
def oBuf : Nat := 2560

/-! ## The entry -/

/-- The arguments into the registers that keep them, with `r12 = r1`. -/
def prologue : List Instr :=
  [.load .d .r14 .r12 (arg 13), mov .r15 .r7, mov .r16 .r3, mov .r17 .r5, .load .d .r18 .r12 (arg 9),
    .load .d .r19 .r12 (arg 10)]

/-! ## The private operation -/

/-- The frame from which `vg_rsa_private_checked` is called: its Parameter
Save Area, with its twelve stack arguments at `r1 + 96`. -/
def privBytes : Nat := 192

/-- Our stack argument `j`, from that frame. -/
def argP (j : Nat) : Nat := privBytes + arg j

/-- `vg_rsa_private_checked`. -/
def privCall : Prog isa := .call "vg_rsa_private_checked" Impl.Rsa.PPC64LE.Priv.code

/-- Its arguments, with `r12 = r1` in its frame: on the stack `p` (`r10`)
and our stack arguments 0 to 8 (`p_len` to `qinv_len`), then the rest of
`scratch` from `oRsa` and `scratch_len - 1024`; in the registers `EM`'s
place (`k` bytes), `n`, `e` and the ciphertext (`k` bytes). -/
def privArgs : List Instr :=
  [.addSp .r12 0, .store .d .r10 .r12 96] ++
    (List.range 9).flatMap (fun j => [.load .d .r0 .r12 (argP j), .store .d .r0 .r12 (104 + 8 * j)]) ++
    [.li .r0 oRsa, .add .r0 .r14 .r0, .store .d .r0 .r12 176, .load .d .r11 .r12 (argP 14),
      .subi .r11 .r11 1024, .store .d .r11 .r12 184, .addi .r3 .r14 oEm, mov .r4 .r15, mov .r5 .r6, mov .r6 .r15,
      mov .r7 .r8, mov .r8 .r9, .load .d .r9 .r12 (argP 11), mov .r10 .r15]

/-- The private operation, from its frame; its result into `r20`,
zero-extended. -/
def priv : Prog isa :=
  .seq (.frame (.alloc privBytes) (.seq (.block privArgs) privCall) (.free privBytes)) (.block [.lsr .w .r20 .r3 0])

variable (H G : Hash)

/-! ## Failing -/

/-- In `r3`, 1 if `k < 2 hLen + 2`, 0 if not. -/
def chkK : List Instr := [.li .r3 (2 * H.D + 2), .sub .r3 .r15 .r3, .lsr .d .r3 .r3 63]

/-- `r3 := (r = 2) ? 2 : 0`, for `r < 2⁶³`. -/
def faultBit : List Instr :=
  [.li .r4 2, .logic .xor .r3 .r20 .r4, .subi .r3 .r3 1, .lsr .d .r3 .r3 63, .add .r3 .r3 .r3]

/-- Zeros to `out` and `*msg_len`, and the result `(r = 2) ? 2 : 0`. -/
def decFail : Prog isa := .seq zeroOut (.block ([.store .d .r6 .r17 0] ++ faultBit))

/-! ## The decoding -/

/-- `H(label)` to `scratch + oDig`. -/
def hashLabel : Prog isa :=
  .seq (.block [.addi .r3 .r14 oSt]) (.seq H.callInit
  (.seq (.block [.addi .r3 .r14 oSt, .li .r4 0, mov .r5 .r18, mov .r6 .r19, .addi .r7 .r14 oW]) (.seq H.callUpd
  (.seq (.block [.addi .r3 .r14 oSt, mov .r4 .r19, .addi .r5 .r14 oDig, .addi .r6 .r14 oW]) H.callFin))))

/-- `acc := EM[0] ∨ ⋁ (lHash'[i] ⊕ lHash[i])`, in `r24`. -/
def accLh : Prog isa :=
  .seq (.block [.addi .r4 .r14 (oEm + 1 + H.D), .addi .r5 .r14 oDig, .lbz .r24 .r14 oEm, .li .r6 H.D])
    (.loop (.block [.lbz .r7 .r4 0, .lbz .r8 .r5 0, .logic .xor .r7 .r7 .r8, .logic .or .r24 .r24 .r7,
      .addi .r4 .r4 1, .addi .r5 .r5 1, .subi .r6 .r6 1]) (.nonzero .d .r6))

/-- `T`'s address in `r4` and its length `t = k - 2 hLen - 1` in `r5`. -/
def tArgs : List Instr := [.addi .r4 .r14 (oEm + 1 + 2 * H.D), .subi .r5 .r15 (2 * H.D + 1)]

/-- A byte `b` of `T` (at `r4`, `r5` left, its index in `r6`): with
`z = (b = 0)` and `o = (b = 1)`, `acc ∨= looking ∧ ((z ∨ o) - 1)`,
`idx ∨= i ∧ looking ∧ -o`, `looking ∧= o - 1`; `looking` (`r7`) is all
ones while no `0x01` has been seen. -/
def scanBody : List Instr :=
  [.lbz .r10 .r4 0, .subi .r8 .r10 1, .lsr .d .r8 .r8 63, .li .r9 1, .logic .xor .r9 .r10 .r9, .subi .r9 .r9 1,
    .lsr .d .r9 .r9 63, .logic .or .r8 .r8 .r9, .subi .r8 .r8 1, .logic .and .r8 .r8 .r7, .logic .or .r24 .r24 .r8,
    .li .r3 0, .sub .r3 .r3 .r9, .logic .and .r8 .r6 .r7, .logic .and .r8 .r8 .r3, .logic .or .r25 .r25 .r8,
    .subi .r9 .r9 1, .logic .and .r7 .r7 .r9, .addi .r4 .r4 1, .addi .r6 .r6 1, .subi .r5 .r5 1]

/-- The scan of `T`, then `acc ∨= looking`. -/
def scan : Prog isa :=
  .seq (.block (tArgs H ++ [.li .r6 0, .li .r7 0, .subi .r7 .r7 1, .li .r25 0]))
    (.seq (.loop (.block scanBody) (.nonzero .d .r5)) (.block [.logic .or .r24 .r24 .r7]))

/-- The buffer's 2048 bytes cleared. -/
def clearBuf : Prog isa := .seq (.block [.addi .r4 .r14 oBuf, .li .r5 2048, .li .r6 0]) zeroLoop

/-- `T` to the buffer. -/
def copyT : Prog isa := .seq (.block (tArgs H ++ [mov .r6 .r5, .addi .r5 .r14 oBuf])) copyLoop

/-- A pass: each of the buffer's first `k` bytes replaced by the one `d`
(`r9`) bytes after it if bit 0 of `a` (`r8`) is set. -/
def shiftPass : Prog isa :=
  .seq (.block [.addi .r4 .r14 oBuf, .add .r5 .r4 .r9, .li .r6 1, .logic .and .r6 .r8 .r6, .li .r7 0,
      .sub .r6 .r7 .r6, mov .r7 .r15])
    (.loop (.block [.lbz .r11 .r4 0, .lbz .r3 .r5 0, .logic .xor .r3 .r3 .r11, .logic .and .r3 .r3 .r6,
      .logic .xor .r11 .r11 .r3, .stb .r11 .r4 0, .addi .r4 .r4 1, .addi .r5 .r5 1, .subi .r7 .r7 1])
      (.nonzero .d .r7))

/-- The buffer shifted left by `idx + 1` (`a`, from `r25`) bytes, in ten
passes, the `j`-th by `d = 2^j`. -/
def shift : Prog isa :=
  .seq (.block [.addi .r8 .r25 1, .li .r9 1, .li .r10 10])
    (.loop (.seq shiftPass (.block [.lsr .d .r8 .r8 1, .add .r9 .r9 .r9, .subi .r10 .r10 1])) (.nonzero .d .r10))

/-- `ok` (`r26`): all ones iff `r = 1` and `acc = 0`. -/
def okMask : List Instr :=
  [.li .r4 1, .logic .xor .r4 .r20 .r4, .subi .r4 .r4 1, .lsr .d .r4 .r4 63, .li .r5 0, .sub .r5 .r5 .r24,
    .logic .or .r5 .r5 .r24, .lsr .d .r5 .r5 63, .li .r6 1, .logic .xor .r5 .r5 .r6, .logic .and .r4 .r4 .r5,
    .li .r26 0, .sub .r26 .r26 .r4]

/-- The buffer's first `k` bytes, ANDed with `ok`, to `out`. -/
def outLoop : Prog isa :=
  .seq (.block [.addi .r4 .r14 oBuf, mov .r5 .r16, mov .r6 .r15])
    (.loop (.block [.lbz .r7 .r4 0, .logic .and .r7 .r7 .r26, .stb .r7 .r5 0, .addi .r4 .r4 1, .addi .r5 .r5 1,
      .subi .r6 .r6 1]) (.nonzero .d .r6))

/-- `*msg_len := (t - idx - 1) ∧ ok`, and the result
`(ok ∧ 1) ∨ ((r = 2) ? 2 : 0)`. -/
def decRet : List Instr :=
  [.subi .r4 .r15 (2 * H.D + 2), .sub .r4 .r4 .r25, .logic .and .r4 .r4 .r26, .store .d .r4 .r17 0] ++
    faultBit ++ [.li .r4 1, .logic .and .r4 .r26 .r4, .logic .or .r3 .r3 .r4]

/-- After the private operation and the check of `k`: the decoding. -/
def decMain : Prog isa :=
  .seq (.block (seedArgs H)) (.seq (mgfXor G) (.seq (.block (dbArgs H)) (.seq (mgfXor G) (.seq (hashLabel H)
  (.seq (accLh H) (.seq (scan H) (.seq clearBuf (.seq (copyT H) (.seq shift (.seq (.block okMask) (.seq outLoop
  (.block (decRet H)))))))))))))

/-! ## The function -/

/-- The frame's body. -/
def body : Prog isa :=
  .seq (.block (save ++ prologue)) (.seq priv (.seq (.block (chkK H))
    (.seq (.ite (.nonzero .d .r3) (decFail) (decMain H G)) (.block restore))))

/-- `vg_rsa_oaep_<H>_mgf1_<G>_decrypt`. -/
def decrypt : Prog isa := .frame (.alloc frameBytes) (body H G) (.free frameBytes)

end VG.Impl.RsaOaep.PPC64LE.Dec
