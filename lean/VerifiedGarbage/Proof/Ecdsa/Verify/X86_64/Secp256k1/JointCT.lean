module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.JointChecks
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Secp256k1.JointContract
public import VerifiedGarbage.Impl.Ecdsa.Verify.Secp256k1.X86_64
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Secp256k1.X86_64.JointLayout

/-! Whole-function timing of secp256k1's joint verification follows the public-input contract. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64.Secp256k1
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Secp256k1.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Secp256k1.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

section
variable (hL : Law Spec.Secp256k1.curve)
    (hT : CombOkW Spec.Secp256k1.curve 9 1 Impl.Secp256k1.secp256k1G9 Impl.Secp256k1.secp256k1G9Start)
    (hI : InvSounds)
include hL hT hI

theorem jointVerify_secp256k1_public_ct :
    ConstantTime isa (VPre secp256k1v) (JointPublic secp256k1v secp256k1GTab)
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify secp256k1v publicJoint (jointDouble publicJoint.K)).inline := by
  have hc := secp256k1v_ok hI
  refine jointVerify_ct_of_points hc joint_before_ct ?_ joint_after_ct
  intro s₀ t₀ ps pt pub
  exact jointPoints_relCT (j := publicJoint) hc hL (jdblOk_dblJ0 hL secp256k1_a0) (.ofGTab rfl hT (by decide) (by decide) rfl) rfl
    (by decide +kernel) joint_add_layout joint_init_layout joint_prep_layout (joint_doubler hc hL)
    joint_mul_checks (fun h => absurd h (by decide)) ps pt pub

theorem jointVerify_ct :
    ConstantTime isa
      (Spec.Ecdsa.Secp256k1.inst.verifyContract (X86_64.abi.withConsts secp256k1v.combConsts)).pre
      (Spec.Ecdsa.Secp256k1.inst.verifyContract (X86_64.abi.withConsts secp256k1v.combConsts)).pub
      Impl.Ecdsa.Verify.X86_64.verifySecp256k1.inline := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact jointVerify_secp256k1_public_ct hL hT hI _ _ _ _ _ _ (pre_of (implies.pre _ pre₁))
    (pre_of (implies.pre _ pre₂)) (jointPublic_of_spec pub) e₁ e₂

end
end VG.Proof.Ecdsa.Verify.X86_64.Secp256k1
