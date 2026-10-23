module

public import VerifiedGarbage.Impl.AesCbc.PPC64LE

/-!
# AES-OFB: PPC64LE implementation

`vg_aes_ofb(schedule = r3, rounds = r4, iv = r5, data = r6, n = r7, scratch = r8)`
(see `VG.Spec.Ofb.aesContract`), composed of calls of the verified
`vg_aes_encrypt_blocks` on one block at a time, as on x86-64
(`VG.Impl.AesOfb.X86_64`).

It is built from AES-CBC's pieces (`Impl/AesCbc/PPC64LE.lean`), whose
arguments are the same: the registers and the return address saved in the
scratch buffer and the arguments kept in `r14` (schedule), `r15` (rounds),
`r16` (the block to continue from), `r17` (the next block), `r18` (blocks
left) and `r19` (scratch). Each block, the block at `iv` is enciphered in
place, giving the next output block, which is XORed into the data block.

Only the pointers, `rounds` and `n` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesOfb.PPC64LE

open VG.PPC64LE
open VG.Impl.AesCbc.PPC64LE (mov whole xorInto advance encCall)

/-- The arguments of the block function for the block at `r16`: the
schedule, the rounds, the block, `n = 1`, and the working space. -/
def ivArgs : List Instr := [mov .r3 .r14, mov .r4 .r15, mov .r5 .r16, .li .r6 1, mov .r7 .r19]

/-- One block: the output block `Oⱼ = CIPH_K(Oⱼ₋₁)` in place, XORed into the
data block. -/
def body : Prog isa := .seq (.block ivArgs) (.seq encCall (.block (xorInto .r17 .r16 ++ advance)))

def crypt : Prog isa := whole body

end VG.Impl.AesOfb.PPC64LE
