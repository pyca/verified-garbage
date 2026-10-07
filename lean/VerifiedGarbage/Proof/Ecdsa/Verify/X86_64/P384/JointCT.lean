import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointChecks

/-! Whole-function timing of P-384's joint verification follows the public-input contract. -/
namespace VG.Proof.Ecdsa.Verify.X86_64.P384
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P384.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.P384.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

section
variable (hL : Law Spec.P384.curve)
    (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : InvSounds)
include hL hT hI

theorem jointVerify_p384_public_ct :
    ConstantTime isa (VPre p384v) (JointPublic p384v p384Table)
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p384v publicJoint (Joint.jacDouble publicJoint.K)) := by
  have hc := p384v_ok hI
  refine jointVerify_ct_of_points hc joint_before_ct ?_ joint_after_ct
  intro s₀ t₀ ps pt pub
  exact jointPoints_relCT hc hL (p384v_tbls hT) rfl rfl rfl rfl (by decide +kernel)
    joint_add_layout joint_init_layout joint_prep_layout (joint_doubler hc hL) joint_mul_checks ps pt pub

theorem jointVerify_p384_adx_public_ct :
    ConstantTime isa (VPre p384vx) (JointPublic p384vx p384Table)
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p384vx publicJointAdx
        (Joint.jacDouble publicJointAdx.K)) := by
  have hc := p384vx_ok hI
  refine jointVerify_ct_of_points hc joint_adx_before_ct ?_ joint_adx_after_ct
  intro s₀ t₀ ps pt pub
  exact jointPoints_relCT hc hL (p384vx_tbls hT) rfl rfl rfl rfl (by decide +kernel)
    joint_adx_add_layout joint_adx_init_layout joint_adx_prep_layout (joint_adx_doubler hc hL)
    joint_adx_mul_checks ps pt pub

theorem jointVerify_ct :
    ConstantTime isa
      (Spec.Ecdsa.P384.inst.verifyContract (X86_64.abi.withConsts p384.combConsts)).pre
      (Spec.Ecdsa.P384.inst.verifyContract (X86_64.abi.withConsts p384.combConsts)).pub
      Impl.Ecdsa.Verify.X86_64.jointVerifyP384 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact jointVerify_p384_public_ct hL hT hI _ _ _ _ _ _ (pre_of (implies.pre _ pre₁))
    (pre_of (implies.pre _ pre₂)) (jointPublic_of_spec pub) e₁ e₂

theorem jointVerify_adx_ct :
    ConstantTime isa
      (Spec.Ecdsa.P384.inst.verifyContract (X86_64.abi.withConsts p384.combConsts)).pre
      (Spec.Ecdsa.P384.inst.verifyContract (X86_64.abi.withConsts p384.combConsts)).pub
      Impl.Ecdsa.Verify.X86_64.jointVerifyP384Adx := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact jointVerify_p384_adx_public_ct hL hT hI _ _ _ _ _ _
    (pre_of_x (implies.pre _ pre₁)) (pre_of_x (implies.pre _ pre₂))
    (show JointPublic p384vx p384Table s₁ s₂ from { jointPublic_of_spec pub with }) e₁ e₂

end
end VG.Proof.Ecdsa.Verify.X86_64.P384
