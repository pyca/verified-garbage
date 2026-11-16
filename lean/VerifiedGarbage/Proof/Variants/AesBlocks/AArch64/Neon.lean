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
  enc := ⟨"vg_aes_encrypt_blocks_neon", Impl.Aes.AArch64.Neon.encryptBlocks⟩
  encNoFrames := by lit_decide
  encOk := Neon.encryptBlocks_correct
  encCt := Neon.encryptBlocks_ct
  encKeepsV := by lit_decide
  dec := ⟨"vg_aes_decrypt_blocks_neon", Impl.Aes.AArch64.Neon.decryptBlocks⟩
  decNoFrames := by lit_decide
  decOk := Neon.decryptBlocks_correct
  decCt := Neon.decryptBlocks_ct
  decKeepsV := by lit_decide
  free := false
  encFree := nofun
  decFree := nofun
  suffix := "_neon"
  features := []
  expand := .scalar
  expandNoFrames := Ctr32Impl.scalar.expandNoFrames
  expandOk := Ctr32Impl.scalar.expandOk
  expandCt := Ctr32Impl.scalar.expandCt
  expandKeepsV := Ctr32Impl.scalar.expandKeepsV

end VG.Proof.Variants.AesBlocks.AArch64
