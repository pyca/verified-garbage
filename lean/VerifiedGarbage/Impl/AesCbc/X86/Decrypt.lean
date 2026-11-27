module

public import VerifiedGarbage.Impl.Aes.X86.AesNiBlocks

/-!
# AES-CBC decryption with AES-NI on x86 (32-bit)

`vg_aes_cbc_decrypt(schedule, rounds, iv, data, n, scratch)`, cdecl (the
arguments are at `[esp + 4]` … `[esp + 24]`), for CPUs with AES-NI: the
blocks are deciphered six at a time (`xmm0`–`xmm5`), then one at a time, as
`vg_aes_decrypt_blocks_aesni` does (`Impl/Aes/X86/AesNiBlocks.lean`, whose
`imcKeys` and `aesDec` these are), with no call for each block.

`eax` holds the schedule, `ecx` the number of rounds, `edx` the scratch
buffer, `esi` the data and `edi` the number of blocks left; `esi` and `edi`,
which are callee-saved, are saved in the scratch buffer's first eight
bytes. `xmm7` holds the chaining value, which no round changes (`xmm6` is
the round key's): each deciphered block is XORed with it, the block's
ciphertext is loaded into it again, and then the plaintext is stored over
the ciphertext (`finish`). The chaining value is stored back at `iv`, whose
address is loaded again from the stack, at the end.

Of the scratch buffer it writes only the first 240 bytes: the two saved
registers, and the round keys through `aesimc` and the last round key
(`imcKeys`). It has no frame and no call.

Every branch and every address depends only on the pointers, `rounds` and
`n`.
-/

@[expose] public section

namespace VG.Impl.AesCbc.X86.Decrypt

open VG.X86
open VG.Impl.Aes.X86.AesNi (at_ argOp loadData regs6 aesDec imcKeys)

/-- `Pⱼ = CIPH⁻¹_K(Cⱼ) ⊕ Cⱼ₋₁` for the deciphered block in `b`, with `Cⱼ₋₁` in
`xmm7`: `Cⱼ` is loaded into `xmm7` again before `Pⱼ` is stored over it. -/
def finish (b : XReg) (j : Nat) : List Instr :=
  [.xop (.bin .pxor b .xmm7), .movdquLoad .xmm7 (at_ .esi (16 * j)), .movdquStore (at_ .esi (16 * j)) b]

/-- `finish` for each block register, from block `j` on. -/
def finishData : List XReg → Nat → List Instr
  | [], _ => []
  | b :: bs, j => finish b j ++ finishData bs (j + 1)

/-- The blocks at `esi` deciphered in the registers `rs`, each XORed with the
ciphertext block before it, and stored; then `advance`. -/
def group (rs : List XReg) (advance : List Instr) : Prog isa :=
  .seq (.block (loadData .esi rs 0)) (.seq (aesDec rs) (.block (finishData rs 0 ++ advance)))

/-- Six blocks. -/
def blocks6 : Prog isa :=
  group regs6 [.alu .add .esi (.imm 96), .alu .sub .edi (.imm 6), .alu .cmp .edi (.imm 6)]

/-- One block. -/
def blocks1 : Prog isa := group [.xmm0] [.alu .add .esi (.imm 16), .alu .sub .edi (.imm 1)]

/-- The blocks, six and then one at a time, after `cmp edi, 6`. -/
def tail : Prog isa :=
  .seq (.ite .b (.block []) (.loop blocks6 .ae))
    (.seq (.block [.alu .test .edi (.reg .edi)]) (.ite .e (.block []) (.loop blocks1 .ne)))

/-- Save `esi` and `edi` in the scratch buffer (argument 5), load the
chaining value (at argument 2) into `xmm7`, and load the other arguments. -/
def prologue : List Instr :=
  [.mov .edx (.mem (argOp 5)), .store (at_ .edx 0) .esi, .store (at_ .edx 4) .edi,
   .mov .eax (.mem (argOp 2)), .movdquLoad .xmm7 (at_ .eax 0),
   .mov .eax (.mem (argOp 0)), .mov .ecx (.mem (argOp 1)), .mov .esi (.mem (argOp 3)),
   .mov .edi (.mem (argOp 4))]

def cmp6 : List Instr := [.alu .cmp .edi (.imm 6)]

/-- Store the chaining value at `iv` (argument 2), and restore `esi` and
`edi`. -/
def epilogue : List Instr :=
  [.mov .eax (.mem (argOp 2)), .movdquStore (at_ .eax 0) .xmm7,
   .mov .esi (.mem (at_ .edx 0)), .mov .edi (.mem (at_ .edx 4))]

def decrypt : Prog isa :=
  .seq (.block prologue) (.seq imcKeys (.seq (.block cmp6) (.seq tail (.block epilogue))))

end VG.Impl.AesCbc.X86.Decrypt
