import VerifiedGarbage.Impl.AesCbc.X86_64

/-!
# AES-CTR: x86-64 implementation

`vg_aes_ctr(schedule = rdi, rounds = rsi, ctr = rdx, data = rcx, n = r8, scratch = r9)`
(see `VG.Spec.Ctr.aesContract`), composed of calls of the verified
`vg_aes_encrypt_blocks` on one block at a time. It is generic over the
implementation it calls (`Blocks`): it is emitted once for each
implementation (e.g. `vg_aes_ctr_aesni` calls `vg_aes_encrypt_blocks_aesni`).

It is built from AES-CBC's pieces (`Impl/AesCbc/X86_64.lean`), whose
arguments are the same: the registers saved in the scratch buffer and the
arguments kept in `rbx` (schedule), `rbp` (rounds), `r12` (the counter
block), `r13` (the next block), `r14` (blocks left) and `r15` (scratch).
Each block, the counter block is copied to the scratch buffer (at 2048,
where CBC's decryption keeps a block) and enciphered there, giving the next
output block, which is XORed into the data block; then the counter block is
incremented as a 128-bit big-endian number: its two halves loaded,
byte-reversed (`bswap`), added to with `add` and `adc`, reversed again and
stored.

Only the pointers, `rounds` and `n` can affect timing.
-/

namespace VG.Impl.AesCtr.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (Blocks)
open VG.Impl.AesCbc.X86_64 (whole copy advance at_ cOff)

/-- The counter block copied to the scratch buffer, and the arguments of the
block function for the copy: the schedule, the rounds, the copy, `n = 1`,
and the working space. -/
def pre : List Instr :=
  copy .r15 cOff .r12 0 ++
    [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r15), .alu .add .rdx (.imm cOff),
     .mov32 .rcx (.imm 1), .mov .r8 (.reg .r15)]

/-- The output block, in the scratch buffer, XORed into the data block. -/
def xorOut : List Instr :=
  [.mov .rax (.mem (at_ .r13 0)), .alu .xor .rax (.mem (at_ .r15 cOff)), .store (at_ .r13 0) .rax,
   .mov .rax (.mem (at_ .r13 8)), .alu .xor .rax (.mem (at_ .r15 (cOff + 8))), .store (at_ .r13 8) .rax]

/-- The counter block plus 1, modulo `2¹²⁸`, big-endian. -/
def incr : List Instr :=
  [.mov .rax (.mem (at_ .r12 8)), .bswap .rax, .mov .rcx (.mem (at_ .r12 0)), .bswap .rcx,
   .alu .add .rax (.imm 1), .alu .adc .rcx (.imm 0), .bswap .rax, .bswap .rcx,
   .store (at_ .r12 8) .rax, .store (at_ .r12 0) .rcx]

/-- One block. -/
def body (b : Blocks) : Prog isa :=
  .seq (.block pre) (.seq (.call b.name b.code) (.block (xorOut ++ incr ++ advance)))

def crypt (b : Blocks) : Prog isa := whole (body b)

end VG.Impl.AesCtr.X86_64
