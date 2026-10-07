import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P224.JointChecks

/-! Whole-function timing of P-224's joint verification follows the public-input contract. -/
namespace VG.Proof.Ecdsa.Verify.X86_64.P224
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P224.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.P224.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

section
variable (hL : Law Spec.P224.curve)
    (hT : CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : InvSounds)
include hL hT hI

theorem jointVerify_p224_public_ct :
    ConstantTime isa (VPre p224v) (JointPublic p224v p224Table)
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p224v publicJoint (Joint.jacDouble publicJoint.K)) := by
  have hc := p224v_ok hI
  refine jointVerify_ct_of_points hc joint_before_ct ?_ joint_after_ct
  intro s₀ t₀ ps pt pub
  exact jointPoints_relCT hc hL (p224v_tbls hT) rfl rfl rfl rfl (by decide +kernel)
    joint_add_layout joint_init_layout joint_prep_layout (joint_doubler hc hL) joint_mul_checks ps pt pub

theorem jointVerify_ct :
    ConstantTime isa
      (Spec.Ecdsa.P224.inst.verifyContract (X86_64.abi.withConsts p224.combConsts)).pre
      (Spec.Ecdsa.P224.inst.verifyContract (X86_64.abi.withConsts p224.combConsts)).pub
      Impl.Ecdsa.Verify.X86_64.jointVerifyP224 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact jointVerify_p224_public_ct hL hT hI _ _ _ _ _ _ (pre_of (implies.pre _ pre₁))
    (pre_of (implies.pre _ pre₂)) (jointPublic_of_spec pub) e₁ e₂

end
end VG.Proof.Ecdsa.Verify.X86_64.P224
