import VerifiedGarbage.Impl.AesCbc.AArch64

/-!
# AES-OFB: AArch64 implementation

`vg_aes_ofb(schedule = x0, rounds = x1, iv = x2, data = x3, n = x4, scratch = x5)`
(see `VG.Spec.Ofb.aesContract`), composed of calls of the verified
`vg_aes_encrypt_blocks` on one block at a time. It is generic over the
implementation it calls (`Blocks`): it is emitted once for each
implementation (e.g. `vg_aes_ofb_aes` calls `vg_aes_encrypt_blocks_aes`).

It is built from AES-CBC's pieces (`Impl/AesCbc/AArch64.lean`), whose
arguments are the same: the registers saved in the scratch buffer and the
arguments kept in `x19` (schedule), `x20` (rounds), `x21` (the block to
continue from), `x22` (the next block), `x23` (blocks left) and `x24`
(scratch). Each block, the block at `iv` is enciphered in place, giving the
next output block, which is XORed into the data block.

Only the pointers, `rounds` and `n` can affect timing.
-/

namespace VG.Impl.AesOfb.AArch64

open VG.AArch64
open VG.Impl.Aes.AArch64 (Blocks)
open VG.Impl.AesCbc.AArch64 (mov whole xorInto advance)

/-- The arguments of the block function for the block at `x21`: the
schedule, the rounds, the block, `n = 1`, and the working space. -/
def ivArgs : List Instr := [mov .x0 .x19, mov .x1 .x20, mov .x2 .x21, .movz .x .x3 1 0, mov .x4 .x24]

/-- One block: the output block `Oⱼ = CIPH_K(Oⱼ₋₁)` in place, XORed into the
data block. -/
def body (b : Blocks) : Prog isa :=
  .seq (.block ivArgs) (.seq (.call b.name b.code) (.block (xorInto ++ advance)))

def crypt (b : Blocks) : Prog isa := whole (body b)

end VG.Impl.AesOfb.AArch64
