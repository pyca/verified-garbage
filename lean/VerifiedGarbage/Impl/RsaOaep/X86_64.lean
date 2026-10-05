import VerifiedGarbage.Impl.Mgf1.X86_64

/-!
# RSAES-OAEP (RFC 8017 §7.1) on x86-64

`encrypt` and `decrypt`, for a hash function `H` (the label's) and MGF1's
hash function `G`, each an `Impl.Pbkdf2.Md.X86_64.Stream` (the streaming
functions of MD5, SHA-1, SHA-224, SHA-256 or the SHA-512 family), calling
those functions, MGF1 (`Impl/Mgf1/X86_64.lean`), and the RSA operation: the
public-key operation within BoringSSL's limits (`vg_rsa_public_checked`)
when encrypting, the private-key operation checked against `e`
(`vg_rsa_private_checked`) when decrypting.

Everything runs in a frame of `frameBytes` bytes: at `rsp`, the stack
arguments of the RSA operation; then the slots, which hold the arguments
and the values the code computes (the callees keep no caller-saved
register). The first `oRsa` = 8192 bytes of `scratch` are ours; the RSA
operation gets the rest, `scratch_len - 1024` words.

## Encryption

`encrypt(out = rdi, out_len = rsi, n = rdx, n_len = rcx, e = r8,
e_len = r9, label, label_len, msg, msg_len, seed, scratch, scratch_len)`,
the last seven on the stack. If `k < 2 hLen + 2` or `msg_len > k - 2 hLen
- 2` (public), it writes zeros to `out` and returns 0. Otherwise it writes
`EM = 0x00 ‖ seed ‖ DB` to `scratch` (`DB = lHash ‖ 0… ‖ 0x01 ‖ M`, the
label hashed with `H`), masks `DB` with MGF1 of the seed and then the seed
with MGF1 of `maskedDB` (`G`), and returns `vg_rsa_public_checked` of `EM`
into `out`.

## Decryption

`decrypt(out = rdi, out_len = rsi, msg_len = rdx, n = rcx, n_len = r8,
e = r9, e_len, p, p_len, q, q_len, dp, dp_len, dq, dq_len, qinv, qinv_len,
label, label_len, ct, ct_len, scratch, scratch_len)`, the last seventeen
on the stack. `vg_rsa_private_checked` writes `EM` (or zeros) to `scratch`
and returns `r` (1, 0 or 2), which only selects values without a branch.
If `k < 2 hLen + 2` (public), the result is `r = 2 ? 2 : 0`, with zeros to
`out` and `*msg_len`. Otherwise, as BoringSSL's
`RSA_padding_check_PKCS1_OAEP_mgf1` without a branch on anything secret:
the label is hashed (`H`), the seed and `DB` unmasked in place (`G`); an
accumulator `acc` ORs together `EM`'s first byte and `lHash' ⊕ lHash`; the
scan over `T = DB[hLen..]` (`t = k - 2 hLen - 1` bytes) finds the index
`idx` of its first nonzero byte with masks, and ORs into `acc` a mask if a
byte before it is not zero or `0x01`, or if there is none; `T` is copied
into the 2048-byte buffer `scratch + oBuf`, zeros after it, and shifted
left by `idx + 1` bytes in ten passes, pass `j` moving every one of its
first 1024 bytes `2^j` bytes under the mask of bit `j` of `idx + 1`: the
message, then zeros. With `ok` all ones exactly when `r = 1` and
`acc = 0`, `out` receives the buffer's first `k` bytes ANDed with `ok`,
`*msg_len` receives `(t - idx - 1) ∧ ok`, and the result is
`(ok ∧ 1) ∨ (r = 2 ? 2 : 0)`.
-/

namespace VG.Impl.RsaOaep.X86_64

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Impl.Mgf1.X86_64 (seqs sp ix at_ step byteLoop Layout mgfXor)

/-! ## The frame -/

/-- The frame: the RSA operation's stack arguments (14 words for the
private operation, 4 for the public one) at `rsp`, then the slots. It is
`≡ 8 (mod 16)`, so that `rsp` is a multiple of 16 at the calls. -/
def frameBytes : Nat := 296

/-- MGF1's slots. -/
def sScr : Nat := 112
def sSrc : Nat := 120
def sSrcLen : Nat := 128
def sDst : Nat := 136
def sDstLen : Nat := 144
def sCtr : Nat := 152
def sDone : Nat := 160
/-- The arguments. -/
def sOut : Nat := 168
def sN : Nat := 176
def sK : Nat := 184
def sE : Nat := 192
def sEl : Nat := 200
def sScrLen : Nat := 208
def sLab : Nat := 216
def sLabLen : Nat := 224
/-- Encryption: the message, its length and the seed. Decryption: the
address of `*msg_len`, the private operation's result and `acc`. -/
def sMsg : Nat := 232
def sMsgLen : Nat := 240
def sSeed : Nat := 248
def sMl : Nat := 232
def sR : Nat := 240
def sAcc : Nat := 248
/-- Decryption: `idx`, `ok`, and the shift's bits, distance and passes. -/
def sIdx : Nat := 256
def sOk : Nat := 264
def sA : Nat := 272
def sD : Nat := 280
def sJ : Nat := 288

/-! ## Our part of `scratch` -/

/-- `EM`: `k` bytes. -/
def oEm : Nat := 0
/-- The buffer in which decryption shifts `T`: 2048 bytes. -/
def oBuf : Nat := 1024
/-- The streaming state (at most 192 bytes). -/
def oSt : Nat := 3072
/-- The digest `finalize` writes (at most 64 bytes). -/
def oDig : Nat := 3328
/-- `lHash`, when decrypting. -/
def oLh : Nat := 3392
/-- MGF1's counter. -/
def oCtr : Nat := 3456
/-- The working space of `update` and `finalize` (at most 2048 bytes). -/
def oW : Nat := 4096
/-- Where the RSA operation's working space starts. -/
def oRsa : Nat := 8192

/-- MGF1's layout. -/
def lay : Layout := ⟨sScr, sSrc, sSrcLen, sDst, sDstLen, sCtr, sDone, oSt, oCtr, oDig, oW⟩

/-- The function's stack argument `j`. -/
def arg (j : Nat) : MemOp := sp (frameBytes + 8 + 8 * j)

/-- `d ← [scratch] + o`. -/
def scr (d : Reg) (o : Nat) : List Instr := Impl.Mgf1.X86_64.scr lay d o

/-- The function's stack argument `j` to the slot `d`. -/
def argSlot (j d : Nat) : List Instr := [.mov .rax (.mem (arg j)), .store (sp d) .rax]

/-- `imm32 n`. -/
def im (n : Nat) : Src := .imm (BitVec.ofNat 32 n)

variable (H G : Stream)

/-! ## Common pieces -/

/-- The label's hash, `H(label)`, to `scratch + o`. -/
def hashLabel (o : Nat) : Prog isa :=
  seqs [.block (scr .rdi oSt), .call H.initN H.initC,
    .block (scr .rdi oSt ++ [.mov32 .rsi (.imm 0), .mov .rdx (.mem (sp sLab)), .mov .rcx (.mem (sp sLabLen))] ++
      scr .r8 oW),
    .call H.updN H.updC,
    .block (scr .rdi oSt ++ [.mov .rsi (.mem (sp sLabLen))] ++ scr .rdx o ++ scr .rcx oW),
    .call H.finN H.finC]

/-- MGF1's slots for masking `DB` (`k - hLen - 1` bytes at `EM + 1 + hLen`)
with the seed (`hLen` bytes at `EM + 1`). -/
def dbArgs : List Instr :=
  scr .rax (oEm + 1 + H.D) ++ [.mov .rdx (.mem (sp sK)), .alu .sub .rdx (im (H.D + 1))] ++ scr .rcx (oEm + 1) ++
    [.mov32 .r9 (im H.D), .store (sp sDst) .rax, .store (sp sDstLen) .rdx, .store (sp sSrc) .rcx,
      .store (sp sSrcLen) .r9]

/-- MGF1's slots for masking the seed with `DB`. -/
def seedArgs : List Instr :=
  scr .rax (oEm + 1) ++ [.mov32 .rdx (im H.D)] ++ scr .rcx (oEm + 1 + H.D) ++
    [.mov .r9 (.mem (sp sK)), .alu .sub .r9 (im (H.D + 1)), .store (sp sDst) .rax, .store (sp sDstLen) .rdx,
      .store (sp sSrc) .rcx, .store (sp sSrcLen) .r9]

/-- `k` zeros to `out`. -/
def zeroOut : Prog isa :=
  .seq (.block [.mov .rdi (.mem (sp sOut)), .mov .r10 (.mem (sp sK)), .mov32 .rax (.imm 0), .mov32 .r8 (.imm 0)])
    (byteLoop [.store8 (ix .rdi .r8) .rax] (.reg .r10))

/-- `k ≥ 2 hLen + 2`: CF set if not, with `k` in `rax`. -/
def chkK : List Instr := [.mov .rax (.mem (sp sK)), .alu .cmp .rax (im (2 * H.D + 2))]

/-! ## Encryption -/

/-- The arguments into their slots. -/
def encPrologue : List Instr :=
  [.store (sp sOut) .rdi, .store (sp sN) .rdx, .store (sp sK) .rcx, .store (sp sE) .r8, .store (sp sEl) .r9] ++
  argSlot 0 sLab ++ argSlot 1 sLabLen ++ argSlot 2 sMsg ++ argSlot 3 sMsgLen ++ argSlot 4 sSeed ++
  argSlot 5 sScr ++ argSlot 6 sScrLen

/-- `msg_len ≤ k - 2 hLen - 2`, from `rax = k`: CF set if not. -/
def chkMsg : List Instr := [.alu .sub .rax (im (2 * H.D + 2)), .alu .cmp .rax (.mem (sp sMsgLen))]

/-- Zeros to `out`, and 0. -/
def encFail : Prog isa := zeroOut

/-- `EM`'s place, the first 1024 bytes of `scratch`, cleared. -/
def clearEm : Prog isa :=
  .seq (.block (scr .rcx oEm ++ [.mov32 .rax (.imm 0), .mov32 .r8 (.imm 0)]))
    (.loop (.block [.store (ix .rcx .r8) .rax, .alu .add .r8 (.imm 8), .alu .cmp .r8 (.imm 1024)]) .ne)

/-- The seed to `EM + 1`. -/
def copySeed : Prog isa :=
  .seq (.block ([.mov .rsi (.mem (sp sSeed))] ++ scr .rcx oEm ++ [.mov32 .r8 (.imm 0)]))
    (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rcx .r8 (oEm + 1)) .rax] (im H.D))

/-- `lHash` (the digest at `scratch + oDig`) to `EM + 1 + hLen`. -/
def copyLh : Prog isa :=
  .seq (.block (scr .rsi oDig ++ scr .rcx oEm ++ [.mov32 .r8 (.imm 0)]))
    (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rcx .r8 (oEm + 1 + H.D)) .rax] (im H.D))

/-- `0x01` at `EM + k - mLen - 1`, and the message after it, if it is not
empty. -/
def putMsg : Prog isa :=
  .seq (.block (scr .rdi oEm ++ [.mov .rax (.mem (sp sK)), .alu .add .rdi (.reg .rax), .mov .rax (.mem (sp sMsgLen)),
      .alu .sub .rdi (.reg .rax),
      .alu .sub .rdi (.imm 1), .mov32 .rax (.imm 1), .store8 (at_ .rdi) .rax, .mov .rsi (.mem (sp sMsg)),
      .mov .r10 (.mem (sp sMsgLen)), .mov32 .r8 (.imm 0), .alu .test .r10 (.reg .r10)]))
    (.ite .e (.block []) (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rdi .r8 1) .rax] (.reg .r10)))

/-- The arguments of `vg_rsa_public_checked`: `out` (`k` bytes), `n`, `e`,
`EM` as the input (`k` bytes), and the rest of `scratch`. -/
def pubArgs : List Instr :=
  scr .rax oEm ++ [.mov .rdx (.mem (sp sK))] ++ scr .rcx oRsa ++
  [.mov .r9 (.mem (sp sScrLen)), .alu .sub .r9 (.imm 1024), .store (sp 0) .rax, .store (sp 8) .rdx,
    .store (sp 16) .rcx, .store (sp 24) .r9,
    .mov .rdi (.mem (sp sOut)), .mov .rsi (.mem (sp sK)), .mov .rdx (.mem (sp sN)), .mov .rcx (.mem (sp sK)),
    .mov .r8 (.mem (sp sE)), .mov .r9 (.mem (sp sEl))]

/-- `EM`, before masking. -/
def encEm : Prog isa := seqs [clearEm, copySeed H, hashLabel H oDig, copyLh H, putMsg]

variable (pubN : String) (pubC : Prog isa)

/-- After the checks. -/
def encMain : Prog isa :=
  seqs [encEm H, .block (dbArgs H), mgfXor lay G, .block (seedArgs H), mgfXor lay G, .block pubArgs,
    .call pubN pubC]

def encBody : Prog isa :=
  seqs [.block (encPrologue ++ chkK H),
    .ite .b encFail (seqs [.block (chkMsg H), .ite .b encFail (encMain H G pubN pubC)])]

/-- `vg_rsa_oaep_<H>_mgf1_<G>_encrypt`. -/
def encrypt : Prog isa := .frame (.alloc frameBytes) (encBody H G pubN pubC) (.free frameBytes)

/-! ## Decryption -/

/-- The arguments into their slots. -/
def decPrologue : List Instr :=
  [.store (sp sOut) .rdi, .store (sp sMl) .rdx, .store (sp sN) .rcx, .store (sp sK) .r8, .store (sp sE) .r9] ++
  argSlot 0 sEl ++ argSlot 11 sLab ++ argSlot 12 sLabLen ++ argSlot 15 sScr ++ argSlot 16 sScrLen

/-- The arguments of `vg_rsa_private_checked`: `EM`'s place (`k` bytes),
`n`, `e`, the ciphertext as the input (`k` bytes), the private key, and the
rest of `scratch`. -/
def privArgs : List Instr :=
  [.mov .rax (.mem (arg 13)), .store (sp 0) .rax, .mov .rax (.mem (sp sK)), .store (sp 8) .rax] ++
  (List.range 10).flatMap (fun j => [.mov .rax (.mem (arg (j + 1))), .store (sp (16 + 8 * j)) .rax]) ++
  scr .rax oRsa ++ [.store (sp 96) .rax, .mov .rax (.mem (sp sScrLen)), .alu .sub .rax (.imm 1024),
    .store (sp 104) .rax] ++
  scr .rdi oEm ++ [.mov .rsi (.mem (sp sK)), .mov .rdx (.mem (sp sN)), .mov .rcx (.mem (sp sK)),
    .mov .r8 (.mem (sp sE)), .mov .r9 (.mem (sp sEl))]

/-- `rax := (r = 2) ? 2 : 0`. -/
def faultBit : List Instr :=
  [.mov .rax (.mem (sp sR)), .alu .xor .rax (.imm 2), .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax),
    .alu .and .rax (.imm 2)]

/-- Zeros to `out` and `*msg_len`, and the result `(r = 2) ? 2 : 0`. -/
def decFail : Prog isa :=
  .seq zeroOut (.block ([.mov .rdi (.mem (sp sMl)), .store (at_ .rdi) .rax] ++ faultBit))

/-- `acc := EM[0] ∨ ⋁ (lHash'[i] ⊕ lHash[i])`. -/
def accLh : Prog isa :=
  .seq (.block (scr .rcx oLh ++ scr .rdi (oEm + 1 + H.D) ++ scr .rsi oEm ++
      [.movzx8 .rdx (at_ .rsi), .mov32 .r8 (.imm 0)]))
    (.seq (byteLoop [.movzx8 .rax (ix .rcx .r8), .movzx8 .r9 (ix .rdi .r8), .alu .xor .rax (.reg .r9),
        .alu .or .rdx (.reg .rax)] (im H.D))
      (.block [.store (sp sAcc) .rdx]))

/-- `T`'s length, `t = k - 2 hLen - 1`, to `r10`. -/
def tLen : List Instr := [.mov .r10 (.mem (sp sK)), .alu .sub .r10 (im (2 * H.D + 1))]

/-- The scan of `T`: `rdx` all ones while no `0x01` has been seen
(`looking`), `rsi` the index of the first, `rcx` the accumulator, ORed with
a mask for every nonzero byte other than `0x01` before it. -/
def scanBody : List Instr :=
  [.movzx8 .rax (ix .rdi .r8),
    .mov .r9 (.reg .rax), .alu .cmp .r9 (.imm 1), .alu .sbb .r9 (.reg .r9),
    .mov .r11 (.reg .rax), .alu .xor .r11 (.imm 1), .alu .cmp .r11 (.imm 1), .alu .sbb .r11 (.reg .r11),
    .mov .rax (.reg .r9), .alu .or .rax (.reg .r11), .alu .xor .rax (.imm 0xFFFFFFFF), .alu .and .rax (.reg .rdx),
    .alu .or .rcx (.reg .rax),
    .mov .rax (.reg .r8), .alu .and .rax (.reg .rdx), .alu .and .rax (.reg .r11), .alu .or .rsi (.reg .rax),
    .alu .xor .r11 (.imm 0xFFFFFFFF), .alu .and .rdx (.reg .r11)]

/-- The scan, then `acc |= looking` and `idx` into its slot. -/
def scan : Prog isa :=
  .seq (.block (scr .rdi (oEm + 1 + 2 * H.D) ++ tLen H ++
      [.mov .rdx (.imm 0xFFFFFFFF), .mov32 .rsi (.imm 0), .mov .rcx (.mem (sp sAcc)), .mov32 .r8 (.imm 0)]))
    (.seq (byteLoop scanBody (.reg .r10))
      (.block [.alu .or .rcx (.reg .rdx), .store (sp sAcc) .rcx, .store (sp sIdx) .rsi]))

/-- The buffer's 2048 bytes cleared. -/
def clearBuf : Prog isa :=
  .seq (.block (scr .rcx oBuf ++ [.mov32 .rax (.imm 0), .mov32 .r8 (.imm 0)]))
    (.loop (.block [.store (ix .rcx .r8) .rax, .alu .add .r8 (.imm 8), .alu .cmp .r8 (.imm 2048)]) .ne)

/-- `T` to the buffer. -/
def copyT : Prog isa :=
  .seq (.block (scr .rsi (oEm + 1 + 2 * H.D) ++ scr .rcx oBuf ++ tLen H ++ [.mov32 .r8 (.imm 0)]))
    (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rcx .r8) .rax] (.reg .r10))

/-- One pass of the shift: each of the buffer's first 1024 bytes replaced by
the one `d` (`sD`) bytes after it if bit 0 of `a` (`sA`) is set. -/
def shiftPass : Prog isa :=
  .seq (.block (scr .rcx oBuf ++ [.mov .rsi (.reg .rcx), .alu .add .rsi (.mem (sp sD)),
      .mov .r11 (.mem (sp sA)), .alu .and .r11 (.imm 1), .mov32 .r9 (.imm 0), .alu .sub .r9 (.reg .r11),
      .mov32 .r8 (.imm 0)]))
    (byteLoop [.movzx8 .rax (ix .rcx .r8), .movzx8 .rdi (ix .rsi .r8), .alu .xor .rdi (.reg .rax),
      .alu .and .rdi (.reg .r9), .alu .xor .rax (.reg .rdi), .store8 (ix .rcx .r8) .rax] (.imm 1024))

/-- The next pass: `a >>= 1`, `d += d`, and ZF set after the tenth. -/
def nextPass : List Instr :=
  [.mov .rax (.mem (sp sA)), .shift .shr .rax 1, .store (sp sA) .rax, .mov .rax (.mem (sp sD)),
    .alu .add .rax (.reg .rax), .store (sp sD) .rax, .mov .rax (.mem (sp sJ)), .alu .sub .rax (.imm 1),
    .store (sp sJ) .rax]

/-- The buffer shifted left by `idx + 1` bytes. -/
def shift : Prog isa :=
  .seq (.block [.mov .rax (.mem (sp sIdx)), .alu .add .rax (.imm 1), .store (sp sA) .rax, .mov32 .rax (.imm 1),
      .store (sp sD) .rax, .mov32 .rax (.imm 10), .store (sp sJ) .rax])
    (.loop (.seq shiftPass (.block nextPass)) .ne)

/-- `ok`: all ones iff `r = 1` and `acc = 0`, to its slot and `r11`. -/
def okMask : List Instr :=
  [.mov .rax (.mem (sp sR)), .alu .xor .rax (.imm 1), .alu .cmp .rax (.imm 1), .alu .sbb .rax (.reg .rax),
    .mov .r11 (.mem (sp sAcc)), .alu .cmp .r11 (.imm 1), .alu .sbb .r11 (.reg .r11), .alu .and .r11 (.reg .rax),
    .store (sp sOk) .r11]

/-- The buffer's first `k` bytes, ANDed with `ok`, to `out`. -/
def outLoop : Prog isa :=
  .seq (.block ([.mov .rdi (.mem (sp sOut))] ++ scr .rcx oBuf ++ [.mov .r10 (.mem (sp sK)),
      .mov .r11 (.mem (sp sOk)), .mov32 .r8 (.imm 0)]))
    (byteLoop [.movzx8 .rax (ix .rcx .r8), .alu .and .rax (.reg .r11), .store8 (ix .rdi .r8) .rax] (.reg .r10))

/-- `*msg_len := (t - idx - 1) ∧ ok`, and the result `(ok ∧ 1) ∨ ((r = 2) ? 2 : 0)`. -/
def decRet : List Instr :=
  [.mov .r11 (.mem (sp sOk)), .mov .rax (.mem (sp sK)), .alu .sub .rax (im (2 * H.D + 2)),
    .alu .sub .rax (.mem (sp sIdx)), .alu .and .rax (.reg .r11), .mov .rdi (.mem (sp sMl)),
    .store (at_ .rdi) .rax, .alu .and .r11 (.imm 1)] ++ faultBit ++ [.alu .or .rax (.reg .r11)]

/-- After the private operation and the check of `k`: the decoding. -/
def decMain : Prog isa :=
  seqs [hashLabel H oLh, .block (seedArgs H), mgfXor lay G, .block (dbArgs H), mgfXor lay G, accLh H, scan H,
    clearBuf, copyT H, shift, .block okMask, outLoop, .block (decRet H)]

variable (privN : String) (privC : Prog isa)

def decBody : Prog isa :=
  seqs [.block (decPrologue ++ privArgs), .call privN privC, .block ([.store (sp sR) .rax] ++ chkK H),
    .ite .b decFail (decMain H G)]

/-- `vg_rsa_oaep_<H>_mgf1_<G>_decrypt`. -/
def decrypt : Prog isa := .frame (.alloc frameBytes) (decBody H G privN privC) (.free frameBytes)

end VG.Impl.RsaOaep.X86_64
