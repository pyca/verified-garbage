module

public import VerifiedGarbage.Impl.AesCbc.X86

/-!
# AES-OFB: x86 (32-bit) implementation

`vg_aes_ofb(schedule, rounds, iv, data, n, scratch)` (see
`VG.Spec.Ofb.aesContract`), every argument on the stack (cdecl), composed of
calls of the verified `vg_aes_encrypt_blocks` on one block at a time. It is
generic over the implementation it calls (`Blocks`): it is emitted once for
each implementation (e.g. `vg_aes_ofb_aesni` calls
`vg_aes_encrypt_blocks_aesni`).

It is built from AES-CBC's pieces (`Impl/AesCbc/X86.lean`), whose arguments
are the same: the registers saved in the scratch buffer, `esi` the next
block, the other arguments reloaded from the stack, and each call in a frame
of its own that pushes the block function's five arguments. Each block, the
block at `iv` is enciphered in place, giving the next output block, which is
XORed into the data block a word at a time.

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

@[expose] public section

namespace VG.Impl.AesOfb.X86

open VG.X86
open VG.Impl.Aes.X86 (Blocks)
open VG.Impl.CmacAes.X86 (argOp advance xor4)
open VG.Impl.AesCbc.X86 (whole blkCall)

/-- The arguments of the block function: the schedule and the rounds (our
stack arguments 0 and 1), the block at `iv` (our stack argument 2), `n = 1`,
and the working space (our stack argument 5). -/
def ivArgs : List Instr :=
  [.mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .ebx (argOp 2), .mov .edi (.imm 1), .mov .ebp (argOp 5)]

/-- The output block XORed into the data block, and on to the next block. -/
def post : List Instr := ([.mov .ebx (argOp 2)] : List Instr) ++ xor4 .esi .ebx .esi 0 0 0 ++ advance

/-- One block: the output block `Oⱼ = CIPH_K(Oⱼ₋₁)` in place, XORed into the
data block. -/
def body (b : Blocks) : Prog isa := .seq (.block ivArgs) (.seq (blkCall b) (.block post))

def crypt (b : Blocks) : Prog isa := whole (body b)

end VG.Impl.AesOfb.X86
