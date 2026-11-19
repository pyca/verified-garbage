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
  scratch := 2048
  scratch_ok := .inr rfl
  okW := by rw [Proof.Aes.ctr32AArch64With_2048]; exact Neon.ctr32N_correct
  ctW := by rw [Proof.Aes.ctr32AArch64With_2048]; exact Neon.ctr32N_ct
  keepsV := by lit_decide
  to := ⟨"vg_aes_ctr32_to_neon", Impl.Aes.AArch64.Neon.ctr32ToN⟩
  toNoFrames := by lit_decide
  toOk := Neon.ctr32ToN_correct
  toCt := Neon.ctr32ToN_ct
  toKeepsV := by lit_decide
  suffix := "_neon"
  features := []
  clear := ⟨[.x1, .x3, .x4, .x6, .x7, .x8, .x9, .x10, .x12],
    [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19, .v20, .v21, .v22, .v23, .v24, .v25,
     .v26, .v27, .v28, .v29, .v30, .v31],
    []⟩
  expand := .scalar
  expandNoFrames := Ctr32Impl.scalar.expandNoFrames
  expandOk := Ctr32Impl.scalar.expandOk
  expandCt := Ctr32Impl.scalar.expandCt
  expandKeepsV := Ctr32Impl.scalar.expandKeepsV

end VG.Proof.Variants.AesCtr32.AArch64
