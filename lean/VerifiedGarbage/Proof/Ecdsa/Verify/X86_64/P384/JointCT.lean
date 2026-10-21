module

public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointChecks
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointContract
public import VerifiedGarbage.Impl.Ecdsa.Verify.P384.X86_64
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.P384.X86_64.JointLayout

/-! Whole-function timing of P-384's joint verification follows the public-input contract. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.P384
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P384.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.P384.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

section
variable (hL : Law Spec.P384.curve)
    (hT : CombOkW Spec.P384.curve 9 1 Impl.P384.p384G9 Impl.P384.p384G9Start)
    (hI : InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P384.curve)
include hL hT hI hO

theorem jointVerify_p384_public_ct :
    ConstantTime isa (VPre p384v) (JointPublic p384v p384GTab)
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p384v publicJoint (jointDouble publicJoint.K)).inline := by
  have hc := p384v_ok hI
  refine jointVerify_ct_of_points hc joint_before_ct ?_ joint_after_ct
  intro s₀ t₀ ps pt pub
  exact jointPoints_relCT hc hL (.ofGTab rfl hT (by decide) (by decide) rfl) rfl (by decide +kernel)
    joint_add_layout joint_init_layout joint_prep_layout (joint_doubler hc hL) joint_mul_checks
    (fun _ => ⟨hO,by decide⟩) ps pt pub

theorem jointVerify_p384_adx_public_ct :
    ConstantTime isa (VPre p384vx) (JointPublic p384vx p384GTab)
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p384vx publicJointAdx
        (jointDoubleAdx publicJointAdx.K)).inline := by
  have hc := p384vx_ok hI
  refine jointVerify_ct_of_points hc joint_adx_before_ct ?_ joint_adx_after_ct
  intro s₀ t₀ ps pt pub
  exact jointPoints_relCT hc hL (.ofGTab rfl hT (by decide) (by decide) rfl) rfl (by decide +kernel)
    joint_adx_add_layout joint_adx_init_layout joint_adx_prep_layout (joint_adx_doubler hc hL)
    joint_adx_mul_checks (fun _ => ⟨hO,by decide⟩) ps pt pub

theorem jointVerify_ct :
    ConstantTime isa
      (Spec.Ecdsa.P384.inst.verifyContract (X86_64.abi.withConsts p384v.combConsts)).pre
      (Spec.Ecdsa.P384.inst.verifyContract (X86_64.abi.withConsts p384v.combConsts)).pub
      Impl.Ecdsa.Verify.X86_64.jointVerifyP384.inline := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact jointVerify_p384_public_ct hL hT hI hO _ _ _ _ _ _ (pre_of (implies.pre _ pre₁))
    (pre_of (implies.pre _ pre₂)) (jointPublic_of_spec pub) e₁ e₂

theorem jointVerify_adx_ct :
    ConstantTime isa
      (Spec.Ecdsa.P384.inst.verifyContract (X86_64.abi.withConsts p384v.combConsts)).pre
      (Spec.Ecdsa.P384.inst.verifyContract (X86_64.abi.withConsts p384v.combConsts)).pub
      Impl.Ecdsa.Verify.X86_64.jointVerifyP384Adx.inline := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact jointVerify_p384_adx_public_ct hL hT hI hO _ _ _ _ _ _
    (pre_of_x (implies.pre _ pre₁)) (pre_of_x (implies.pre _ pre₂))
    (show JointPublic p384vx p384GTab s₁ s₂ from { jointPublic_of_spec pub with }) e₁ e₂

end
end VG.Proof.Ecdsa.Verify.X86_64.P384
