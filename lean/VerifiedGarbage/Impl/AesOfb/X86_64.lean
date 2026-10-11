module

public import VerifiedGarbage.Impl.AesCbc.X86_64

/-!
# AES-OFB: x86-64 implementation

`vg_aes_ofb(schedule = rdi, rounds = rsi, iv = rdx, data = rcx, n = r8, scratch = r9)`
(see `VG.Spec.Ofb.aesContract`), composed of calls of the verified
`vg_aes_encrypt_blocks` on one block at a time. It is generic over the
implementation it calls (`Blocks`): it is emitted once for each
implementation (e.g. `vg_aes_ofb_aesni` calls
`vg_aes_encrypt_blocks_aesni`).

It is built from AES-CBC's pieces (`Impl/AesCbc/X86_64.lean`), whose
arguments are the same: the registers saved in the scratch buffer and the
arguments kept in `rbx` (schedule), `rbp` (rounds), `r12` (the block to
continue from), `r13` (the next block), `r14` (blocks left) and `r15`
(scratch). Each block, the block at `iv` is enciphered in place, giving the
next output block, which is XORed into the data block.

Only the pointers, `rounds` and `n` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesOfb.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (Blocks)
open VG.Impl.AesCbc.X86_64 (whole xorInto advance)

/-- The arguments of the block function for the block at `r12`: the
schedule, the rounds, the block, `n = 1`, and the working space. -/
def ivArgs : List Instr :=
  [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r12), .mov32 .rcx (.imm 1),
   .mov .r8 (.reg .r15)]

/-- One block: the output block `Oⱼ = CIPH_K(Oⱼ₋₁)` in place, XORed into the
data block. -/
def body (b : Blocks) : Prog isa :=
  .seq (.block ivArgs) (.seq (.call b.name b.code) (.block (xorInto .r13 .r12 ++ advance)))

def crypt (b : Blocks) : Prog isa := whole (body b)

end VG.Impl.AesOfb.X86_64
