module

public import VerifiedGarbage.Impl.AesCbc.RISCV64

/-!
# AES-OFB: RISC-V implementation

`vg_aes_ofb(schedule = a0, rounds = a1, iv = a2, data = a3, n = a4, scratch = a5)`
(see `VG.Spec.Ofb.aesContract`), composed of calls of the verified
`vg_aes_encrypt_blocks` on one block at a time, as on PPC64LE
(`VG.Impl.AesOfb.PPC64LE`).

It is built from AES-CBC's pieces (`Impl/AesCbc/RISCV64.lean`), whose
arguments are the same: the registers and the return address saved in the
scratch buffer and the arguments kept in `s1` (schedule), `s2` (rounds),
`s3` (the block to continue from), `s4` (the next block), `s5` (blocks left)
and `s6` (scratch). Each block, the block at `iv` is enciphered in place,
giving the next output block, which is XORed into the data block.

Only the pointers, `rounds` and `n` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesOfb.RISCV64

open VG.RISCV64
open VG.Impl.AesCbc.RISCV64 (mov whole xorInto advance encCall chainWrapped)

/-- The arguments of the block function for the block at `s3`: the
schedule, the rounds, the block, `n = 1`, and the working space. -/
def ivArgs : List Instr := [mov .a0 .s1, mov .a1 .s2, mov .a2 .s3, .li .a3 1, mov .a4 .s6]

/-- One block: the output block `Oⱼ = CIPH_K(Oⱼ₋₁)` in place, XORed into the
data block. -/
def body : Prog isa := .seq (.block ivArgs) (.seq encCall (.block (xorInto .s4 .s3 ++ advance)))

/-- Each output block `Oⱼ = CIPH_K(Oⱼ₋₁)` XORed into the data, by the OFB
chain (`Impl.Aes.RISCV64.ofbChain`), which bitslices the round keys once
for all the blocks. -/
def crypt : Prog isa := chainWrapped Impl.Aes.RISCV64.ofbChainCall

end VG.Impl.AesOfb.RISCV64
