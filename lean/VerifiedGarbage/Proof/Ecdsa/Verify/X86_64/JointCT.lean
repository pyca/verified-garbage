module

public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointChecks
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitErase
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointContract
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
import VerifiedGarbage.Proof.P256.X86_64.JointInitLayout
import VerifiedGarbage.Proof.P256.X86_64.JointPrep
import VerifiedGarbage.Proof.P256.X86_64.JointLayout
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified

/-! Whole-function timing follows the public-input contract for baseline and ADX. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P256.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.P256.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

section
variable (hL : Law Spec.P256.curve)
    (hT : CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P256.curve)
include hL hT hI hO

theorem jointVerify_p256_public_ct :
    ConstantTime isa (VPre p256) (JointPublic p256 p256Table)
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p256 publicJoint (jointDouble publicJoint.K)).inline := by
  have hc := p256_ok hI
  refine jointVerify_ct_of_points hc joint_before_ct ?_ joint_after_ct
  intro s₀ t₀ ps pt pub
  exact jointPoints_relCT hc hL (.ofComb rfl hT (by decide) (by decide) rfl) rfl (by decide +kernel)
    joint_add_layout joint_init_layout joint_prep_layout (joint_doubler hc hL) joint_mul_checks
    (fun _ => ⟨hO,by decide⟩) ps pt pub

theorem jointVerify_p256_adx_public_ct :
    ConstantTime isa (VPre p256x) (JointPublic p256x p256Table)
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p256x publicJointAdx (jointDouble publicJointAdx.K)).inline := by
  have hc := p256x_ok hI
  refine jointVerify_ct_of_points hc joint_adx_before_ct ?_ joint_adx_after_ct
  intro s₀ t₀ ps pt pub
  exact jointPoints_relCT hc hL (.ofComb rfl hT (by decide) (by decide) rfl) rfl (by decide +kernel)
    joint_adx_add_layout joint_adx_init_layout joint_adx_prep_layout (joint_adx_doubler hc hL)
    joint_adx_mul_checks (fun _ => ⟨hO,by decide⟩) ps pt pub

theorem jointVerify_ct :
    ConstantTime isa
      (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts)).pre
      (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts)).pub
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p256 publicJoint (jointDouble publicJoint.K)).inline := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact jointVerify_p256_public_ct hL hT hI hO _ _ _ _ _ _ (pre_of (implies.pre _ pre₁))
    (pre_of (implies.pre _ pre₂)) (jointPublic_of_spec pub) e₁ e₂

theorem jointVerify_adx_ct :
    ConstantTime isa
      (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts)).pre
      (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256.combConsts)).pub
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p256x publicJointAdx (jointDouble publicJointAdx.K)).inline := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact jointVerify_p256_adx_public_ct hL hT hI hO _ _ _ _ _ _
    (show VPre p256x s₁ from { pre_of (implies.pre _ pre₁) with })
    (show VPre p256x s₂ from { pre_of (implies.pre _ pre₂) with })
    (show JointPublic p256x p256Table s₁ s₂ from { jointPublic_of_spec pub with }) e₁ e₂

end
end VG.Proof.Ecdsa.Verify.X86_64
