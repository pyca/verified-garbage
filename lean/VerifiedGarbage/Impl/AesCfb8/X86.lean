module

public import VerifiedGarbage.Impl.AesCbc.X86
public import VerifiedGarbage.Impl.AesCbc.X86.Groups
public import VerifiedGarbage.Impl.Scrub.X86

/-!
# AES-CFB8: x86 (32-bit) implementation

`vg_aes_cfb8_encrypt(schedule, rounds, iv, data, len, scratch)` and
`vg_aes_cfb8_decrypt` with the same arguments (see
`VG.Spec.Cfb8.aesEncryptContract` and `aesDecryptContract`), every argument
on the stack (cdecl), composed of calls of the verified
`vg_aes_encrypt_blocks`. They are generic over the implementation they call
(`Blocks`): each is emitted once for each implementation (e.g.
`vg_aes_cfb8_encrypt_aesni` calls `vg_aes_encrypt_blocks_aesni`).

Encryption calls the block function on one block at a time. It is built
from AES-CBC's pieces (`Impl/AesCbc/X86.lean`), whose arguments are in the
same places, with `len` counting bytes: the registers saved in the scratch
buffer, `esi` the next byte, the other arguments reloaded from the stack,
and each call in a frame of its own that pushes the block function's five
arguments. Each byte, the input block is copied to the scratch buffer (at
`cOff`, zeroed and XORed with it) and enciphered there, its first byte is
XORed into the data byte, and the input block is shifted left by a byte,
with the ciphertext byte shifted in.

Decryption knows every input block before the first call, so it takes as
many as 64 bytes a call (`groups`), as CBC's does blocks
(`Impl/AesCbc/X86/Groups.lean`, whose registers, arguments and frame it
has). Each group of `m` bytes, 64 of them or those left, whichever is fewer:

1. the input block, in `xmm0`, is copied to `buf` and shifted left by a byte,
   with the ciphertext byte shifted in, `m` times (`fillBody`); what is left
   is the next group's, and goes to `iv`;
2. one call of the block function on the `m` blocks of `buf`, in place;
3. the first byte of each block is XORed into the data (`xorBody`).

Only the pointers, `rounds` and `len` can affect timing: the only branches
are on `len`.
-/

@[expose] public section

namespace VG.Impl.AesCfb8.X86

open VG.X86
open VG.Impl.Aes.X86 (Blocks)
open VG.Impl.CmacAes.X86 (argOp at_ xor4 zero4)
open VG.Impl.AesCbc.X86 (cOff whole blkCall)

/-- The input block copied to `ebp + cOff`, and the arguments of the block
function: the schedule and the rounds (our stack arguments 0 and 1), the
copy, `n = 1`, and the working space (our stack argument 5). -/
def pre : List Instr :=
  ([.mov .ebp (argOp 5), .mov .ebx (argOp 2)] : List Instr) ++ zero4 .ebp cOff ++ xor4 .ebp .ebx .ebp cOff 0 cOff ++
  ([.mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .ebx (.reg .ebp), .alu .add .ebx (.imm 2048),
   .mov .edi (.imm 1)] : List Instr)

/-- The input block at `ebx` shifted left by a byte, with `al` shifted in:
the words at `ebx + 1`, `+ 5`, `+ 9` and `+ 12` stored at `ebx`, `+ 4`,
`+ 8` and `+ 11`. -/
def shift : List Instr :=
  [.mov .ecx (.mem (at_ .ebx 1)), .mov .edx (.mem (at_ .ebx 5)), .mov .edi (.mem (at_ .ebx 9)),
   .mov .ebp (.mem (at_ .ebx 12)), .store (at_ .ebx 0) .ecx, .store (at_ .ebx 4) .edx,
   .store (at_ .ebx 8) .edi, .store (at_ .ebx 11) .ebp, .store8 (at_ .ebx 15) .al]

/-- On to the next byte; ZF is set once `esi` reaches `data + len`. -/
def advance : List Instr :=
  [.alu .add .esi (.imm 1), .mov .eax (argOp 4), .alu .add .eax (argOp 3), .alu .cmp .esi (.reg .eax)]

/-- `C#ⱼ = P#ⱼ ⊕ MSB₈(Oⱼ)`, shifted into the input block. -/
def encPost : List Instr :=
  ([.mov .ebp (argOp 5), .movzx8 .eax (at_ .esi 0), .movzx8 .ecx (at_ .ebp cOff), .alu .xor .eax (.reg .ecx),
   .store8 (at_ .esi 0) .al, .mov .ebx (argOp 2)] : List Instr) ++ shift ++ advance

/-- One byte: the input block enciphered in the scratch buffer, and `encPost`. -/
def body (b : Blocks) : Prog isa := .seq (.block pre) (.seq (blkCall b) (.block encPost))

def encrypt (b : Blocks) : Prog isa := whole (body b)

/-! ## Decryption -/

namespace Groups

open VG.Impl.AesCbc.X86.Groups (setup restore size fillPre)

/-- One input block to `buf`, and the next into `xmm0`: shifted left by a
byte, with the ciphertext byte shifted in. -/
def fillBody : List Instr :=
  [.movdquStore (at_ .edx 0) .xmm0, .movzx8 .ebp (at_ .eax 0), .xop (.movd .xmm1 .ebp),
   .xop (.shift .psrldq .xmm0 1), .xop (.shift .pslldq .xmm1 15), .xop (.bin .por .xmm0 .xmm1),
   .alu .add .eax (.imm 1), .alu .add .edx (.imm 16), .alu .sub .ecx (.imm 1)]

/-- The next group's input block to `iv`, and the arguments of the block
function: the schedule, the rounds, `buf`, the number of blocks (in `ebx`)
and the working space. -/
def callArgs : List Instr :=
  [.mov .ebp (argOp 2), .movdquStore (at_ .ebp 0) .xmm0, .mov .eax (argOp 0), .mov .ecx (argOp 1),
   .mov .edx (argOp 6), .mov .ebp (argOp 5)]

/-- Everything before the call. -/
def fill : Prog isa :=
  .seq size (.seq (.block fillPre) (.seq (.loop (.block fillBody) .ne) (.block callArgs)))

/-- `buf` in `edx`, and the number of bytes in `ebp`. -/
def xorPre : List Instr := [.mov .edx (argOp 6), .mov .ebp (.reg .ebx)]

/-- The first byte of one block of `buf` XORed into the data. -/
def xorBody : List Instr :=
  [.movzx8 .eax (at_ .esi 0), .movzx8 .ecx (at_ .edx 0), .alu .xor .eax (.reg .ecx),
   .store8 (at_ .esi 0) .al, .alu .add .esi (.imm 1), .alu .add .edx (.imm 16), .alu .sub .ebp (.imm 1)]

/-- Everything after the call; ZF set if no bytes are left. -/
def finish : Prog isa :=
  .seq (.block xorPre) (.seq (.loop (.block xorBody) .ne) (.block [.alu .sub .edi (.reg .ebx)]))

/-- One group. -/
def body (b : Blocks) : Prog isa := .seq fill (.seq (Impl.AesOcb.X86.blocksFrame ⟨b.name, b.code⟩) finish)

/-- The whole function, with `buf` its seventh argument. -/
def groups (b : Blocks) : Prog isa :=
  .seq (.block setup) (.seq (.ite .e (.block []) (.loop (body b) .ne)) (.block restore))

end Groups

/-- Decryption, with `buf` on the stack. -/
def decrypt (b : Blocks) : Prog isa :=
  Impl.StackScratch.X86.withStackScratch Impl.AesCbc.X86.Groups.bufFrame 6 (Groups.groups b)

end VG.Impl.AesCfb8.X86

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubAll rb W`): the `W`
bytes of stack below `esp` that it and its callees use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue. -/

namespace VG.Impl.AesCfb8.X86.Fn

open VG.X86
open VG.Impl.Aes.X86 (Blocks)

/-- `vg_aes_cfb8_encrypt` over the block function `b`, as emitted. -/
def encrypt (b : Blocks) : Prog isa := Impl.Scrub.X86.scrubAll 0 24 (Impl.AesCfb8.X86.encrypt b)

/-- `vg_aes_cfb8_decrypt` over the block function `b`, as emitted. -/
def decrypt (b : Blocks) : Prog isa := Impl.Scrub.X86.scrubAll 0 1108 (Impl.AesCfb8.X86.decrypt b)

end VG.Impl.AesCfb8.X86.Fn
