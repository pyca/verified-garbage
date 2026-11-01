module

public import VerifiedGarbage.Impl.AesOfb.RISCV64

/-!
# AES-CFB128: RISC-V implementation

`vg_aes_cfb128_encrypt(schedule = a0, rounds = a1, iv = a2, data = a3, n = a4, scratch = a5)`
and `vg_aes_cfb128_decrypt` with the same arguments (see
`VG.Spec.Cfb.aesEncryptContract` and `aesDecryptContract`): each a call of a
function that takes the same arguments and the first 2048 bytes of the
scratch buffer, and bitslices the round keys once for all the blocks,
wrapped as AES-CBC's (`Impl.AesCbc.RISCV64.chainWrapped`):

* encryption, of the CFB128 chain (`Impl.Aes.RISCV64.cfbChain`,
  `Impl/Aes/RISCV64/Chain.lean`): each block `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, in
  place, and the last the block at `iv`;
* decryption, of the wide CFB128 decryption (`Impl.Aes.RISCV64.cfbDecWide`,
  `Impl/Aes/RISCV64/Wide.lean`), four blocks at a time, as the inputs of
  the block cipher are the ciphertext blocks before: each block
  `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)`, in place, and the last `Cⱼ` the block at `iv`.

Only the pointers, `rounds` and `n` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCfb.RISCV64

open VG.RISCV64
open VG.Impl.AesCbc.RISCV64 (chainWrapped)

/-- Each block `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, by the CFB128 chain
(`Impl.Aes.RISCV64.cfbChain`), which bitslices the round keys once for all
the blocks. -/
def encrypt : Prog isa := chainWrapped Impl.Aes.RISCV64.cfbChainCall

/-- Four blocks at a time, by the wide CFB128 decryption
(`Impl.Aes.RISCV64.cfbDecWide`), which bitslices the round keys once. -/
def decrypt : Prog isa := chainWrapped Impl.Aes.RISCV64.cfbDecWideCall

end VG.Impl.AesCfb.RISCV64
