module

public import VerifiedGarbage.Impl.AesCbc.X86_64

/-!
# AES-CFB8: x86-64 implementation

`vg_aes_cfb8_encrypt(schedule = rdi, rounds = rsi, iv = rdx, data = rcx, len = r8, scratch = r9)`
and `vg_aes_cfb8_decrypt` with the same arguments (see
`VG.Spec.Cfb8.aesEncryptContract` and `aesDecryptContract`), composed of
calls of the verified `vg_aes_encrypt_blocks` on one block at a time. They
are generic over the implementation they call (`Blocks`): each is emitted
once for each implementation (e.g. `vg_aes_cfb8_encrypt_aesni` calls
`vg_aes_encrypt_blocks_aesni`).

They are built from AES-CBC's pieces (`Impl/AesCbc/X86_64.lean`), whose
arguments are the same but for `len` counting bytes: the registers saved in
the scratch buffer and the arguments kept in `rbx` (schedule), `rbp`
(rounds), `r12` (the input block), `r13` (the next byte), `r14` (bytes
left) and `r15` (scratch). Each byte, the input block is copied to the
scratch buffer (at `cOff`) and enciphered there, its first byte is XORed
into the data byte, and the input block is shifted left by a byte, with the
ciphertext byte (the output when encrypting, the input when decrypting)
shifted in.

Only the pointers, `rounds` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCfb8.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (Blocks)
open VG.Impl.AesCbc.X86_64 (at_ cOff copy whole)

/-- The input block copied to `r15 + cOff`, and the arguments of the block
function for it: the schedule, the rounds, the block, `n = 1`, and the
working space. -/
def pre : List Instr :=
  copy .r15 cOff .r12 0 ++
  ([.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (.imm cOff),
   .mov32 .rcx (.imm 1), .mov .r8 (.reg .r15)] : List Instr)

/-- The input block at `r12` shifted left by a byte, with `al` shifted in:
the words at `r12 + 1` and `r12 + 8` stored at `r12` and `r12 + 7`. -/
def shift : List Instr :=
  [.mov .rcx (.mem (at_ .r12 1)), .mov .rdx (.mem (at_ .r12 8)), .store (at_ .r12 0) .rcx,
   .store (at_ .r12 7) .rdx, .store8 (at_ .r12 15) .rax]

/-- On to the next byte (ZF is set when none are left). -/
def advance : List Instr := [.alu .add .r13 (.imm 1), .alu .sub .r14 (.imm 1)]

/-- `C#ⱼ = P#ⱼ ⊕ MSB₈(Oⱼ)`, shifted into the input block. -/
def encPost : List Instr :=
  ([.movzx8 .rax (at_ .r13 0), .movzx8 .rcx (at_ .r15 cOff), .alu .xor .rax (.reg .rcx),
   .store8 (at_ .r13 0) .rax] : List Instr) ++ shift ++ advance

/-- `P#ⱼ = C#ⱼ ⊕ MSB₈(Oⱼ)`, and `C#ⱼ` shifted into the input block. -/
def decPost : List Instr :=
  ([.movzx8 .rax (at_ .r13 0), .movzx8 .rcx (at_ .r15 cOff), .alu .xor .rcx (.reg .rax),
   .store8 (at_ .r13 0) .rcx] : List Instr) ++ shift ++ advance

/-- One byte: the input block enciphered in the scratch buffer, and `post`. -/
def body (b : Blocks) (post : List Instr) : Prog isa :=
  .seq (.block pre) (.seq (.call b.name b.code) (.block post))

def encrypt (b : Blocks) : Prog isa := whole (body b encPost)

def decrypt (b : Blocks) : Prog isa := whole (body b decPost)

end VG.Impl.AesCfb8.X86_64
