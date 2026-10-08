import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P521.JointChecks

/-! Whole-function timing of P-521's joint verification follows the public-input contract. -/
namespace VG.Proof.Ecdsa.Verify.X86_64.P521
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P521.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.P521.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64.P521 (p521_ok p521x_ok p521_tbls p521x_tbls)

section
variable (hL : Law Spec.P521.curve)
    (hT : CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : InvSounds)
include hL hT hI

theorem jointVerify_p521_public_ct :
    ConstantTime isa (VPre p521) (JointPublic p521 p521Table)
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p521 publicJoint (Joint.jacDouble publicJoint.K)).inline := by
  have hc := p521_ok hI
  refine jointVerify_ct_of_points hc joint_before_ct ?_ joint_after_ct
  intro s₀ t₀ ps pt pub
  exact jointPoints_relCT hc hL (p521_tbls hT) rfl rfl rfl rfl (by decide +kernel)
    joint_add_layout joint_init_layout joint_prep_layout (joint_doubler hc hL) joint_mul_checks ps pt pub

theorem jointVerify_p521_adx_public_ct :
    ConstantTime isa (VPre p521x) (JointPublic p521x p521Table)
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p521x publicJointAdx
        (Joint.jacDouble publicJointAdx.K)).inline := by
  have hc := p521x_ok hI
  refine jointVerify_ct_of_points hc joint_adx_before_ct ?_ joint_adx_after_ct
  intro s₀ t₀ ps pt pub
  exact jointPoints_relCT hc hL (p521x_tbls hT) rfl rfl rfl rfl (by decide +kernel)
    joint_adx_add_layout joint_adx_init_layout joint_adx_prep_layout (joint_adx_doubler hc hL)
    joint_adx_mul_checks ps pt pub

theorem jointVerify_ct :
    ConstantTime isa
      (Spec.Ecdsa.P521.inst.verifyContract (X86_64.abi.withConsts p521.combConsts)).pre
      (Spec.Ecdsa.P521.inst.verifyContract (X86_64.abi.withConsts p521.combConsts)).pub
      Impl.Ecdsa.Verify.X86_64.jointVerifyP521.inline := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact jointVerify_p521_public_ct hL hT hI _ _ _ _ _ _ (pre_of (implies.pre _ pre₁))
    (pre_of (implies.pre _ pre₂)) (jointPublic_of_spec pub) e₁ e₂

theorem jointVerify_adx_ct :
    ConstantTime isa
      (Spec.Ecdsa.P521.inst.verifyContract (X86_64.abi.withConsts p521.combConsts)).pre
      (Spec.Ecdsa.P521.inst.verifyContract (X86_64.abi.withConsts p521.combConsts)).pub
      Impl.Ecdsa.Verify.X86_64.jointVerifyP521Adx.inline := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact jointVerify_p521_adx_public_ct hL hT hI _ _ _ _ _ _
    (pre_of_x (implies.pre _ pre₁)) (pre_of_x (implies.pre _ pre₂))
    (jointPublic_x (jointPublic_of_spec pub)) e₁ e₂

end
end VG.Proof.Ecdsa.Verify.X86_64.P521
