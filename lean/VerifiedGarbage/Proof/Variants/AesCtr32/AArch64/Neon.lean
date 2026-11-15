module

public import VerifiedGarbage.Proof.Aes.AArch64.Variant
public import VerifiedGarbage.Proof.Aes.AArch64.Neon.Ctr32
import VerifiedGarbage.Proof.Aes.AArch64.Neon.Lit
meta import VerifiedGarbage.Proof.Aes.AArch64.Variant
meta import VerifiedGarbage.Proof.Aes.AArch64.Neon.Ctr32
meta import VerifiedGarbage.Proof.Aes.AArch64.Neon.Lit

/-! # `AesCtr32` bitsliced in AdvSIMD registers on AArch64 -/

@[expose] public section

namespace VG.Proof.Variants.AesCtr32.AArch64

open VG.Proof.Aes.AArch64

/-- `vg_aes_ctr32_neon` and its out-of-place form `vg_aes_ctr32_to_neon`:
eight blocks at a time, bitsliced in AdvSIMD registers, with the baseline
`vg_aes_expand_key`. -/
def neon : Ctr32Impl where
  callee := ⟨"vg_aes_ctr32_neon", Impl.Aes.AArch64.Neon.ctr32N⟩
  noFrames := by lit_decide
  ok := Neon.ctr32N_correct
  ct := Neon.ctr32N_ct
  keepsV := by lit_decide
  to := ⟨"vg_aes_ctr32_to_neon", Impl.Aes.AArch64.Neon.ctr32ToN⟩
  toNoFrames := by lit_decide
  toOk := Neon.ctr32ToN_correct
  toCt := Neon.ctr32ToN_ct
  toKeepsV := by lit_decide
  suffix := "_neon"
  features := []
  expand := .scalar
  expandNoFrames := Ctr32Impl.scalar.expandNoFrames
  expandOk := Ctr32Impl.scalar.expandOk
  expandCt := Ctr32Impl.scalar.expandCt
  expandKeepsV := Ctr32Impl.scalar.expandKeepsV

end VG.Proof.Variants.AesCtr32.AArch64
