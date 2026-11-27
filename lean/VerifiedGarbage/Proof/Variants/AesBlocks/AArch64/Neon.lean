module

public import VerifiedGarbage.Proof.Aes.AArch64.BlocksVariant
public import VerifiedGarbage.Proof.Aes.AArch64.Neon.Blocks
import VerifiedGarbage.Proof.Aes.AArch64.Neon.Lit
meta import VerifiedGarbage.Proof.Aes.AArch64.BlocksVariant
meta import VerifiedGarbage.Proof.Aes.AArch64.Neon.Blocks
meta import VerifiedGarbage.Proof.Aes.AArch64.Neon.Lit

/-! # `AesBlocks` bitsliced in AdvSIMD registers on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.AesBlocks.AArch64

open VG.Proof.Aes.AArch64

/-- `vg_aes_encrypt_blocks_neon` and `vg_aes_decrypt_blocks_neon`: eight
blocks at a time, bitsliced in AdvSIMD registers, with the baseline
`vg_aes_expand_key`. -/
def neon : BlocksImpl where
  enc := ⟨"vg_aes_encrypt_blocks_neon", Impl.Aes.AArch64.Neon.encryptBlocks,
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10],
     [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
      .v26, .v27, .v28, .v29, .v30, .v31],
     []⟩, 2048⟩
  encNoFrames := by lit_decide
  encOk := Neon.encryptBlocks_correct
  encCt := Neon.encryptBlocks_ct
  encKeepsV := by lit_decide
  dec := ⟨"vg_aes_decrypt_blocks_neon", Impl.Aes.AArch64.Neon.decryptBlocks,
    ⟨[.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10],
     [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
      .v26, .v27, .v28, .v29, .v30, .v31],
     []⟩, 2048⟩
  decNoFrames := by lit_decide
  decOk := Neon.decryptBlocks_correct
  decCt := Neon.decryptBlocks_ct
  decKeepsV := by lit_decide
  scratch := 2048
  scratch_ok := .inr rfl
  encScratch_eq := rfl
  decScratch_eq := rfl
  encOkW := by rw [Proof.Aes.blocksAArch64With_2048]; exact Neon.encryptBlocks_correct
  encCtW := by rw [Proof.Aes.blocksAArch64With_2048]; exact Neon.encryptBlocks_ct
  decOkW := by rw [Proof.Aes.blocksAArch64With_2048]; exact Neon.decryptBlocks_correct
  decCtW := by rw [Proof.Aes.blocksAArch64With_2048]; exact Neon.decryptBlocks_ct
  encFree := fun h => absurd h (by decide)
  decFree := fun h => absurd h (by decide)
  encRes := fun h => absurd h (by decide)
  decRes := fun h => absurd h (by decide)
  suffix := "_neon"
  features := []
  encScrub := by lit_decide
  decScrub := by lit_decide
  expand := .scalar
  expandNoFrames := Ctr32Impl.scalar.expandNoFrames
  expandOk := Ctr32Impl.scalar.expandOk
  expandCt := Ctr32Impl.scalar.expandCt
  expandKeepsV := Ctr32Impl.scalar.expandKeepsV
  expandScrub := Ctr32Impl.scalar.expandScrub

end VG.Proof.Variants.AesBlocks.AArch64
