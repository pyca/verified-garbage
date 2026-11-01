module

public import VerifiedGarbage.Impl.AesOfb.RISCV64

/-!
# AES-CFB128: RISC-V implementation

`vg_aes_cfb128_encrypt(schedule = a0, rounds = a1, iv = a2, data = a3, n = a4, scratch = a5)`
and `vg_aes_cfb128_decrypt` with the same arguments (see
`VG.Spec.Cfb.aesEncryptContract` and `aesDecryptContract`), composed of calls
of the verified `vg_aes_encrypt_blocks` on one block at a time, as on PPC64LE
(`VG.Impl.AesCfb.PPC64LE`).

It is built from AES-CBC's and AES-OFB's pieces (`Impl/AesCbc/RISCV64.lean`,
`Impl/AesOfb/RISCV64.lean`), whose arguments are the same: each block, the
block at `iv` (the previous ciphertext block, or the IV) is enciphered in
place, and then the output block is XORed into the data block, and the
ciphertext block is put at `iv`, copied for encryption or as the output
block XORed with the plaintext block for decryption.

Only the pointers, `rounds` and `n` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCfb.RISCV64

open VG.RISCV64
open VG.Impl.AesCbc.RISCV64 (whole xorInto copy advance encCall chainWrapped)
open VG.Impl.AesOfb.RISCV64 (ivArgs)

/-- One block: the block at `iv` enciphered in place, and `post`. -/
def body (post : List Instr) : Prog isa := .seq (.block ivArgs) (.seq encCall (.block post))

/-- `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, and `Cⱼ` the block to continue from. -/
def encPost : List Instr := xorInto .s4 .s3 ++ copy .s3 .s4 ++ advance

/-- `Pⱼ = Cⱼ ⊕ CIPH_K(Cⱼ₋₁)`, and `Cⱼ` the block to continue from. -/
def decPost : List Instr := xorInto .s4 .s3 ++ xorInto .s3 .s4 ++ advance

/-- Each block `Cⱼ = Pⱼ ⊕ CIPH_K(Cⱼ₋₁)`, by the CFB128 chain
(`Impl.Aes.RISCV64.cfbChain`), which bitslices the round keys once for all
the blocks. -/
def encrypt : Prog isa := chainWrapped Impl.Aes.RISCV64.cfbChainCall

def decrypt : Prog isa := whole (body decPost)

end VG.Impl.AesCfb.RISCV64
