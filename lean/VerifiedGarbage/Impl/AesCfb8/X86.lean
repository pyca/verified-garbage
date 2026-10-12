module

public import VerifiedGarbage.Impl.AesCbc.X86

/-!
# AES-CFB8: x86 (32-bit) implementation

`vg_aes_cfb8_encrypt(schedule, rounds, iv, data, len, scratch)` and
`vg_aes_cfb8_decrypt` with the same arguments (see
`VG.Spec.Cfb8.aesEncryptContract` and `aesDecryptContract`), every argument
on the stack (cdecl), composed of calls of the verified
`vg_aes_encrypt_blocks` on one block at a time. They are generic over the
implementation they call (`Blocks`): each is emitted once for each
implementation (e.g. `vg_aes_cfb8_encrypt_aesni` calls
`vg_aes_encrypt_blocks_aesni`).

They are built from AES-CBC's pieces (`Impl/AesCbc/X86.lean`), whose
arguments are in the same places, with `len` counting bytes: the registers
saved in the scratch buffer, `esi` the next byte, the other arguments
reloaded from the stack, and each call in a frame of its own that pushes the
block function's five arguments. Each byte, the input block is copied to
the scratch buffer (at `cOff`, zeroed and XORed with it) and enciphered
there, its first byte is XORed into the data byte, and the input block is
shifted left by a byte, with the ciphertext byte (the output when
encrypting, the input when decrypting) shifted in.

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

/-- `P#ⱼ = C#ⱼ ⊕ MSB₈(Oⱼ)`, and `C#ⱼ` shifted into the input block. -/
def decPost : List Instr :=
  ([.mov .ebp (argOp 5), .movzx8 .eax (at_ .esi 0), .movzx8 .ecx (at_ .ebp cOff), .alu .xor .ecx (.reg .eax),
   .store8 (at_ .esi 0) .cl, .mov .ebx (argOp 2)] : List Instr) ++ shift ++ advance

/-- One byte: the input block enciphered in the scratch buffer, and `post`. -/
def body (b : Blocks) (post : List Instr) : Prog isa := .seq (.block pre) (.seq (blkCall b) (.block post))

def encrypt (b : Blocks) : Prog isa := whole (body b encPost)

def decrypt (b : Blocks) : Prog isa := whole (body b decPost)

end VG.Impl.AesCfb8.X86
