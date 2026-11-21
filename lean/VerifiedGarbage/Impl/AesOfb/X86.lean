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

With AES-NI the code is not around the block function (`cryptNi`): as
AES-CBC's encryption has it (`Impl.AesCbc.X86.encryptNi`), the output block
is loaded into `xmm0` once, enciphered there for each block with no call
(`Impl.Aes.X86.AesNi.aes`, the round keys through `xmm6`) and XORed into the
data block through `xmm7`, and stored at `iv` once after the last block. It
uses no stack, and of the scratch buffer it writes only where it saves the
registers, which it zeroes before returning.

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n` and, with AES-NI, on `rounds`.
-/

@[expose] public section

namespace VG.Impl.AesOfb.X86

open VG.X86
open VG.Impl.Aes.X86 (Blocks)
open VG.Impl.CmacAes.X86 (argOp at_ advance xor4 setup restore niPre niPost)
open VG.Impl.AesCbc.X86 (whole blkCall zeroSaved)

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

/-- One block with AES-NI: the output block in `xmm0` enciphered there (the
round keys through `xmm6`) and XORed into the block at `esi` (through
`xmm7`), and on to the next block; ZF is set when none is left. -/
def niBody : Prog isa :=
  .seq (Impl.Aes.X86.AesNi.aes [.xmm0])
    (.block [.movdquLoad .xmm7 (at_ .esi 0), .xop (.bin .pxor .xmm7 .xmm0), .movdquStore (at_ .esi 0) .xmm7,
      .alu .add .esi (.imm 16), .alu .sub .edi (.imm 1)])

/-- `vg_aes_ofb` with AES-NI: the output block loaded into `xmm0`, the
blocks, and the output block stored, leaving the scratch buffer as it was
but for the zeros where it saved the registers. -/
def cryptNi : Prog isa :=
  .seq (.block setup)
    (.seq (.ite .e (.block []) (.seq (.block niPre) (.seq (.loop niBody .ne) (.block niPost))))
      (.block (restore 5 ++ zeroSaved)))

end VG.Impl.AesOfb.X86
