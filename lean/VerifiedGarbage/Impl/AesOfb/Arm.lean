module

public import VerifiedGarbage.Impl.AesCbc.Arm

/-!
# AES-OFB: 32-bit ARM implementation

`vg_aes_ofb(schedule = r0, rounds = r1, iv = r2, data = r3, n = [sp], scratch = [sp + 4])`
(see `VG.Spec.Ofb.aesContract`), composed of calls of the verified
`vg_aes_encrypt_blocks` on one block at a time.

It is built from AES-CBC's pieces (`Impl/AesCbc/Arm.lean`), whose arguments
are the same: the registers saved in the scratch buffer, the arguments kept
in `r4` (schedule), `r5` (rounds), `r6` (the block to continue from), `r7`
(the next block), `r8` (blocks left) and `r10` (scratch), and each call in a
frame that pushes the working space (8 bytes of stack). Each block, the
block at `iv` is enciphered in place, giving the next output block, which
is XORed into the data block a word at a time.

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

@[expose] public section

namespace VG.Impl.AesOfb.Arm

open VG.Arm
open VG.Impl.CmacAes.Arm (mov advance xor4)
open VG.Impl.AesCbc.Arm (whole encFrame)

/-- The arguments of the block function for the block at `r6`: the
schedule, the rounds, the block, `n = 1`, and the working space. -/
def ivArgs : List Instr := [mov .r0 .r4, mov .r1 .r5, mov .r2 .r6, .mov .r3 (.imm 1), mov .r12 .r10]

/-- The output block XORed into the data block, and on to the next block. -/
def post : List Instr := xor4 .r7 .r6 .r7 0 0 0 ++ advance

/-- One block: the output block `Oⱼ = CIPH_K(Oⱼ₋₁)` in place, XORed into the
data block. -/
def body : Prog isa := .seq (.block ivArgs) (.seq encFrame (.block post))

def crypt : Prog isa := whole body

end VG.Impl.AesOfb.Arm
