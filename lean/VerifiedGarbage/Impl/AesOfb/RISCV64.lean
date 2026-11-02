module

public import VerifiedGarbage.Impl.AesCbc.RISCV64

/-!
# AES-OFB: RISC-V implementation

`vg_aes_ofb(schedule = a0, rounds = a1, iv = a2, data = a3, n = a4, scratch = a5)`
(see `VG.Spec.Ofb.aesContract`): a call of the OFB chain
(`Impl.Aes.RISCV64.ofbChain`, `Impl/Aes/RISCV64/Chain.lean`), which takes
the same arguments and the first 2048 bytes of the scratch buffer, and
bitslices the round keys once for all the blocks: each block, the output
block `Oⱼ = CIPH_K(Oⱼ₋₁)` is XORed into the data block, and the last one
written to `iv`. The call is wrapped as AES-CBC encryption's
(`Impl.AesCbc.RISCV64.chainWrapped`).

Only the pointers, `rounds` and `n` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesOfb.RISCV64

open VG.RISCV64
open VG.Impl.AesCbc.RISCV64 (chainWrapped)

/-- Each output block `Oⱼ = CIPH_K(Oⱼ₋₁)` XORed into the data, by the OFB
chain (`Impl.Aes.RISCV64.ofbChain`), which bitslices the round keys once
for all the blocks. -/
def crypt : Prog isa := chainWrapped Impl.Aes.RISCV64.ofbChainCall

end VG.Impl.AesOfb.RISCV64
