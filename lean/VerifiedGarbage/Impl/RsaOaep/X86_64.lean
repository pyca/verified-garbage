module

public import VerifiedGarbage.Impl.Mgf1.X86_64
public import VerifiedGarbage.Impl.Dispatch.X86_64

/-!
# RSAES-OAEP (RFC 8017 §7.1) on x86-64

`encrypt` and `decrypt`, for the hash function `H` (the label's) and MGF1's
hash function `G` that the selectors `hash` and `mgf1_hash` name (SHA-1 or
a SHA-2 function), calling their streaming functions through the tables
`hash_fns` and `mgf1_fns` (`Spec/HashFns.lean`), MGF1
(`Impl/Mgf1/X86_64.lean`), and the RSA
operation: the public-key operation within BoringSSL's limits
(`vg_rsa_public_checked`) when encrypting, the private-key operation
checked against `e` (`vg_rsa_private_checked`) when decrypting.

Everything runs in a frame of `frameBytes` bytes: at `rsp`, the stack
arguments of the RSA operation; then the slots, which hold the arguments
and the values the code computes (the callees keep no caller-saved
register). The first `oRsa` = 8192 bytes of `scratch` are ours; the RSA
operation gets the rest, `scratch_len - 1024` words.

## The hash functions

The selectors and the tables are the last four arguments, on the stack;
after the other arguments, the code (`selPrologue`) copies each selector to
a slot (`sSelH`, `sSelG`), the lengths it computes with from `hLen` to slots
of their own (`sHD` = `hLen`, `sH1` = `hLen + 1`, `sH2` = `2 hLen + 1`,
`sH3` = `2 hLen + 2`, and `sGD`, MGF1's `hLen`), choosing them by a dispatch
on the selector (`Dispatch.X86_64.chain`, over `lens`), and each table's
three addresses to three slots (`sFnH`, `sFnG`). Each call of a streaming
function is an indirect call of the address in its slot
(`Mgf1.X86_64.initF`, …).

## Encryption

`encrypt(out = rdi, out_len = rsi, n = rdx, n_len = rcx, e = r8,
e_len = r9, label, label_len, msg, msg_len, seed, seed_len, scratch,
scratch_len, …, hash, mgf1_hash, hash_fns, mgf1_fns)`, all but the first six on
the stack. If `k < 2 hLen + 2` or `msg_len > k - 2 hLen
- 2` (public), it writes zeros to `out` and returns 0. Otherwise it writes
`EM = 0x00 ‖ seed ‖ DB` to `scratch` (`DB = lHash ‖ 0… ‖ 0x01 ‖ M`, the
label hashed with `H`), masks `DB` with MGF1 of the seed and then the seed
with MGF1 of `maskedDB` (`G`), and returns `vg_rsa_public_checked` of `EM`
into `out`.

## Decryption

`decrypt(out = rdi, out_len = rsi, msg_len = rdx, n = rcx, n_len = r8,
e = r9, e_len, p, p_len, q, q_len, dp, dp_len, dq, dq_len, qinv, qinv_len,
label, label_len, ct, ct_len, scratch, scratch_len, hash, mgf1_hash, hash_fns,
mgf1_fns)`, the last twenty-one on the stack. `vg_rsa_private_checked` writes `EM` (or zeros) to `scratch`
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

@[expose] public section

namespace VG.Impl.RsaOaep.X86_64

open VG.X86_64
open VG.Impl.Mgf1.X86_64 (seqs sp ix at_ step byteLoop Layout mgfXor initF updF finF)

/-! ## The frame -/

/-- The frame: the RSA operation's stack arguments (14 words for the
private operation, 4 for the public one) at `rsp`, then the slots. It is
`≡ 8 (mod 16)`, so that `rsp` is a multiple of 16 at the calls. -/
def frameBytes : Nat := 408

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
/-- Decryption: `idx`, `ok`, and the shift's bits. -/
def sIdx : Nat := 256
def sOk : Nat := 264
def sA : Nat := 272
/-- The selectors of `H` and `G`, and the lengths computed from their
digests' (`hLen`): `hLen`, `hLen + 1`, `2 hLen + 1` and `2 hLen + 2` of
`H`, and `hLen` of `G`. -/
def sSelH : Nat := 296
def sSelG : Nat := 304
def sHD : Nat := 312
def sH1 : Nat := 320
def sH2 : Nat := 328
def sH3 : Nat := 336
def sGD : Nat := 344
/-- The addresses of `H`'s and `G`'s streaming functions, three slots each. -/
def sFnH : Nat := 360
def sFnG : Nat := 384

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
def lay : Layout := ⟨sScr, sSrc, sSrcLen, sDst, sDstLen, sCtr, sDone, sFnG, sGD, oSt, oCtr, oDig, oW⟩

/-- The function's stack argument `j`. -/
def arg (j : Nat) : MemOp := sp (frameBytes + 8 + 8 * j)

/-- `d ← [scratch] + o`. -/
def scr (d : Reg) (o : Nat) : List Instr := Impl.Mgf1.X86_64.scr lay d o

/-- The function's stack argument `j` to the slot `d`. -/
def argSlot (j d : Nat) : List Instr := [.mov .rax (.mem (arg j)), .store (sp d) .rax]

/-- `imm32 n`. -/
def im (n : Nat) : Src := .imm (BitVec.ofNat 32 n)

/-! ## The hash functions' selectors, lengths and functions -/

/-- The hash functions' numbers and digest lengths: SHA-1 (1) and the SHA-2
functions (2 to 7), as `Spec.HashId.mgf1` numbers them. -/
def lens : List (Nat × Nat) := [(1, 20), (2, 28), (3, 32), (4, 48), (5, 64), (6, 28), (7, 32)]

/-- `hLen` and the lengths computed from it, of the hash function of digest
length `D`, to their slots. -/
def consts (D : Nat) : List Instr :=
  [.mov32 .rax (im D), .store (sp sHD) .rax, .mov32 .rax (im (D + 1)), .store (sp sH1) .rax,
    .mov32 .rax (im (2 * D + 1)), .store (sp sH2) .rax, .mov32 .rax (im (2 * D + 2)), .store (sp sH3) .rax]

/-- The three words of the table the stack argument `j` points to, to the
slots from `d`. -/
def fnSlots (j d : Nat) : List Instr :=
  [.mov .rax (.mem (arg j)), .mov .r10 (.mem (at_ .rax)), .store (sp d) .r10,
    .mov .r10 (.mem (at_ .rax 8)), .store (sp (d + 8)) .r10, .mov .r10 (.mem (at_ .rax 16)),
    .store (sp (d + 16)) .r10]

/-- The selectors, the stack arguments `jH` and `jG`, to their slots, and
the lengths of the hash functions they name to theirs, by a dispatch over
`ls` (numbers and digest lengths); then the tables' words, the stack
arguments `jG + 1` and `jG + 2`, to theirs. -/
def selPrologueWith (ls : List (Nat × Nat)) (jH jG : Nat) : Prog isa :=
  seqs [.block (argSlot jH sSelH),
    Dispatch.X86_64.chain (ls.map fun (i, D) => (i, .block (consts D))),
    .block (argSlot jG sSelG),
    Dispatch.X86_64.chain (ls.map fun (i, D) => (i, .block [.mov32 .rax (im D), .store (sp sGD) .rax])),
    .block (fnSlots (jG + 1) sFnH ++ fnSlots (jG + 2) sFnG)]

/-- `selPrologueWith` over `lens`. -/
def selPrologue (jH jG : Nat) : Prog isa := selPrologueWith lens jH jG

/-! ## Common pieces -/

/-- The label's hash, `H(label)`, to `scratch + o`. -/
def hashLabel (o : Nat) : Prog isa :=
  seqs [.block (scr .rdi oSt), initF sFnH,
    .block (scr .rdi oSt ++ [.mov32 .rsi (.imm 0), .mov .rdx (.mem (sp sLab)), .mov .rcx (.mem (sp sLabLen))] ++
      scr .r8 oW),
    updF sFnH,
    .block (scr .rdi oSt ++ [.mov .rsi (.mem (sp sLabLen))] ++ scr .rdx o ++ scr .rcx oW),
    finF sFnH]

/-- MGF1's slots for masking `DB` (`k - hLen - 1` bytes at `EM + 1 + hLen`)
with the seed (`hLen` bytes at `EM + 1`). -/
def dbArgs : List Instr :=
  scr .rax (oEm + 1) ++ [.alu .add .rax (.mem (sp sHD)), .mov .rdx (.mem (sp sK)), .alu .sub .rdx (.mem (sp sH1))] ++
    scr .rcx (oEm + 1) ++
    [.mov .r9 (.mem (sp sHD)), .store (sp sDst) .rax, .store (sp sDstLen) .rdx, .store (sp sSrc) .rcx,
      .store (sp sSrcLen) .r9]

/-- MGF1's slots for masking the seed with `DB`. -/
def seedArgs : List Instr :=
  scr .rax (oEm + 1) ++ [.mov .rdx (.mem (sp sHD))] ++ scr .rcx (oEm + 1) ++
    [.alu .add .rcx (.mem (sp sHD)), .mov .r9 (.mem (sp sK)), .alu .sub .r9 (.mem (sp sH1)), .store (sp sDst) .rax,
      .store (sp sDstLen) .rdx, .store (sp sSrc) .rcx, .store (sp sSrcLen) .r9]

/-- `k` zeros to `out`. -/
def zeroOut : Prog isa :=
  .seq (.block [.mov .rdi (.mem (sp sOut)), .mov .r10 (.mem (sp sK)), .mov32 .rax (.imm 0), .mov32 .r8 (.imm 0)])
    (byteLoop [.store8 (ix .rdi .r8) .rax] (.reg .r10))

/-- `k ≥ 2 hLen + 2`: CF set if not, with `k` in `rax`. -/
def chkK : List Instr := [.mov .rax (.mem (sp sK)), .alu .cmp .rax (.mem (sp sH3))]

/-! ## Encryption -/

/-- The arguments into their slots. -/
def encPrologue : List Instr :=
  [.store (sp sOut) .rdi, .store (sp sN) .rdx, .store (sp sK) .rcx, .store (sp sE) .r8, .store (sp sEl) .r9] ++
  argSlot 0 sLab ++ argSlot 1 sLabLen ++ argSlot 2 sMsg ++ argSlot 3 sMsgLen ++ argSlot 4 sSeed ++
  argSlot 6 sScr ++ argSlot 7 sScrLen

/-- `msg_len ≤ k - 2 hLen - 2`, from `rax = k`: CF set if not. -/
def chkMsg : List Instr := [.alu .sub .rax (.mem (sp sH3)), .alu .cmp .rax (.mem (sp sMsgLen))]

/-- Zeros to `out`, and 0. -/
def encFail : Prog isa := zeroOut

/-- `EM`'s place, the first 1024 bytes of `scratch`, cleared. -/
def clearEm : Prog isa :=
  .seq (.block (scr .rcx oEm ++ [.mov32 .rax (.imm 0), .mov32 .r8 (.imm 0)]))
    (.loop (.block [.store (ix .rcx .r8) .rax, .alu .add .r8 (.imm 8), .alu .cmp .r8 (.imm 1024)]) .ne)

/-- The seed to `EM + 1`. -/
def copySeed : Prog isa :=
  .seq (.block ([.mov .rsi (.mem (sp sSeed))] ++ scr .rcx oEm ++ [.mov .r10 (.mem (sp sHD)), .mov32 .r8 (.imm 0)]))
    (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rcx .r8 (oEm + 1)) .rax] (.reg .r10))

/-- `lHash` (the digest at `scratch + oDig`) to `EM + 1 + hLen`. -/
def copyLh : Prog isa :=
  .seq (.block (scr .rsi oDig ++ scr .rcx (oEm + 1) ++
      [.mov .r10 (.mem (sp sHD)), .alu .add .rcx (.reg .r10), .mov32 .r8 (.imm 0)]))
    (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rcx .r8) .rax] (.reg .r10))

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
def encEm : Prog isa := seqs [clearEm, copySeed, hashLabel oDig, copyLh, putMsg]

variable (pubN : String) (pubC : Prog isa)

/-- After the checks. -/
def encMain : Prog isa :=
  seqs [encEm, .block dbArgs, mgfXor lay, .block seedArgs, mgfXor lay, .block pubArgs,
    .call pubN pubC]

/-- The selectors and the tables (the stack arguments 10 to 13), the
prologue and the checks, then `main`. -/
def encBodyWith (main : Prog isa) : Prog isa :=
  seqs [.block encPrologue, selPrologue 10 11, .block chkK, .ite .b encFail
    (seqs [.block chkMsg, .ite .b encFail main])]

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
  .seq (.block (scr .rcx oLh ++ scr .rdi (oEm + 1) ++ [.mov .r10 (.mem (sp sHD)), .alu .add .rdi (.reg .r10)] ++
      scr .rsi oEm ++ [.movzx8 .rdx (at_ .rsi), .mov32 .r8 (.imm 0)]))
    (.seq (byteLoop [.movzx8 .rax (ix .rcx .r8), .movzx8 .r9 (ix .rdi .r8), .alu .xor .rax (.reg .r9),
        .alu .or .rdx (.reg .rax)] (.reg .r10))
      (.block [.store (sp sAcc) .rdx]))

/-- `T`'s length, `t = k - 2 hLen - 1`, to `r10` (through `rax`, so that the
taint analysis sees it public). -/
def tLen : List Instr := [.mov .r10 (.mem (sp sK)), .mov .rax (.mem (sp sH2)), .alu .sub .r10 (.reg .rax)]

/-- `d += 2 hLen + 1`, `T`'s offset in `EM`. -/
def tOff (d : Reg) : List Instr := [.mov .rax (.mem (sp sH2)), .alu .add d (.reg .rax)]

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
  .seq (.block (scr .rdi oEm ++ tOff .rdi ++ tLen ++
      [.mov .rdx (.imm 0xFFFFFFFF), .mov32 .rsi (.imm 0), .mov .rcx (.mem (sp sAcc)), .mov32 .r8 (.imm 0)]))
    (.seq (byteLoop scanBody (.reg .r10))
      (.block [.alu .or .rcx (.reg .rdx), .store (sp sAcc) .rcx, .store (sp sIdx) .rsi]))

/-- The buffer's 2048 bytes cleared, with `T`'s address and length in `rsi`
and `r10` and the buffer's in `rcx` for `copyT` and `shift` after it, which
store through them and so cannot read the frame's public slots. -/
def clearBuf : Prog isa :=
  .seq (.block (scr .rsi oEm ++ tOff .rsi ++ tLen ++ scr .rcx oBuf ++ [.mov32 .rax (.imm 0),
      .mov32 .r8 (.imm 0)]))
    (.loop (.block [.store (ix .rcx .r8) .rax, .alu .add .r8 (.imm 8), .alu .cmp .r8 (.imm 2048)]) .ne)

/-- `T` (at `rsi`, `r10` bytes) to the buffer (at `rcx`). -/
def copyT : Prog isa :=
  .seq (.block [.mov32 .r8 (.imm 0)])
    (byteLoop [.movzx8 .rax (ix .rsi .r8), .store8 (ix .rcx .r8) .rax] (.reg .r10))

/-- One pass of the shift, with the buffer at `rcx`: each of its first 1024
bytes replaced by the one `d` (`rdx`) bytes after it if bit 0 of `a` (`sA`)
is set. -/
def shiftPass : Prog isa :=
  .seq (.block [.mov .rsi (.reg .rdx), .alu .add .rsi (.reg .rcx),
      .mov .r11 (.mem (sp sA)), .alu .and .r11 (.imm 1), .mov32 .r9 (.imm 0), .alu .sub .r9 (.reg .r11),
      .mov32 .r8 (.imm 0)])
    (byteLoop [.movzx8 .rax (ix .rcx .r8), .movzx8 .rdi (ix .rsi .r8), .alu .xor .rdi (.reg .rax),
      .alu .and .rdi (.reg .r9), .alu .xor .rax (.reg .rdi), .store8 (ix .rcx .r8) .rax] (.imm 1024))

/-- The next pass: `a >>= 1`, `d += d`, and ZF set after the tenth (the
passes left in `r10`). The distance and the passes stay in registers, the
buffer's address in `rcx`, so that the passes, which store through `rcx`,
read only `a` from the frame. -/
def nextPass : List Instr :=
  [.mov .rax (.mem (sp sA)), .shift .shr .rax 1, .store (sp sA) .rax, .alu .add .rdx (.reg .rdx),
    .alu .sub .r10 (.imm 1)]

/-- The buffer (at `rcx`) shifted left by `idx + 1` bytes. -/
def shift : Prog isa :=
  .seq (.block [.mov .rax (.mem (sp sIdx)), .alu .add .rax (.imm 1), .store (sp sA) .rax,
      .mov32 .rdx (.imm 1), .mov32 .r10 (.imm 10)])
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
  [.mov .r11 (.mem (sp sOk)), .mov .rax (.mem (sp sK)), .alu .sub .rax (.mem (sp sH3)),
    .alu .sub .rax (.mem (sp sIdx)), .alu .and .rax (.reg .r11), .mov .rdi (.mem (sp sMl)),
    .store (at_ .rdi) .rax, .alu .and .r11 (.imm 1)] ++ faultBit ++ [.alu .or .rax (.reg .r11)]

/-- After the private operation and the check of `k`: the decoding. -/
def decMain : Prog isa :=
  seqs [hashLabel oLh, .block seedArgs, mgfXor lay, .block dbArgs, mgfXor lay, accLh, scan,
    clearBuf, copyT, shift, .block okMask, outLoop, .block decRet]

variable (privN : String) (privC : Prog isa)

/-- The selectors and the tables (the stack arguments 17 to 20), the
prologue, the private operation and the check of `k`, then the decoding. -/
def decBody : Prog isa :=
  seqs [.block decPrologue, selPrologue 17 18, .block privArgs, .call privN privC,
    .block ([.mov32 .rax (.reg .rax), .store (sp sR) .rax] ++ chkK),
    .ite .b decFail decMain]

/-- `vg_rsa_oaep_decrypt`. -/
def decrypt : Prog isa := .frame (.alloc frameBytes) (decBody privN privC) (.free frameBytes)

end VG.Impl.RsaOaep.X86_64
