module

public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Hash
import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
meta import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Hash
meta import VerifiedGarbage.Proof.Ecdsa.Verify.Curves
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Spec.Ecdsa.P256
public import VerifiedGarbage.Spec.Ecdsa.Verify.Generic
public import VerifiedGarbage.Proof.Weierstrass.X86_64.InvSpec
public import VerifiedGarbage.Impl.Ecdsa.Verify.P256.X86_64.Joint
public import VerifiedGarbage.Proof.Weierstrass.CombW
public import VerifiedGarbage.TCB.X86_64.Target

import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointAbi
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointErased
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointLit
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Lit
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitErase
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointContract
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
import VerifiedGarbage.Proof.P256.X86_64.JointInitLayout
import VerifiedGarbage.Proof.P256.X86_64.JointPrep
import VerifiedGarbage.Proof.P256.X86_64.JointLayout
import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
/-! The joint implementation satisfies the unchanged shared verification contract. -/

-- Formerly `VerifiedGarbage/Proof/Ecdsa/Verify/X86_64/JointCT.lean`, which only this module imported.
section

/-! Whole-function timing follows the public-input contract for baseline and ADX. -/

section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P256.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.P256.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

section
variable (hL : Law Spec.P256.curve)
    (hT : CombOkW Spec.P256.curve 9 1 Impl.P256.p256G9 Impl.P256.p256G9Start)
    (hI : InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P256.curve)
include hL hT hI hO

theorem jointVerify_p256_public_ct :
    ConstantTime isa (VPre p256v) (JointPublic p256v p256GTab)
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p256v publicJoint (jointDouble publicJoint.K)).inline := by
  have hc := p256v_ok hI
  refine jointVerify_ct_of_points hc joint_before_ct ?_ joint_after_ct
  intro s₀ t₀ ps pt pub
  exact jointPoints_relCT hc.toBaseCfgOk hL (hc.jdbl hL) (.ofGTab rfl hT (by decide) (by decide) rfl) rfl (by decide +kernel)
    joint_add_layout joint_init_layout joint_prep_layout (joint_doubler hc hL) joint_mul_checks
    (fun _ => ⟨hO,by decide,hc.am3⟩) ps pt pub

theorem jointVerify_p256_adx_public_ct :
    ConstantTime isa (VPre p256vx) (JointPublic p256vx p256GTab)
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p256vx publicJointAdx (jointDouble publicJointAdx.K)).inline := by
  have hc := p256vx_ok hI
  refine jointVerify_ct_of_points hc joint_adx_before_ct ?_ joint_adx_after_ct
  intro s₀ t₀ ps pt pub
  exact jointPoints_relCT hc.toBaseCfgOk hL (hc.jdbl hL) (.ofGTab rfl hT (by decide) (by decide) rfl) rfl (by decide +kernel)
    joint_adx_add_layout joint_adx_init_layout joint_adx_prep_layout (joint_adx_doubler hc hL)
    joint_adx_mul_checks (fun _ => ⟨hO,by decide,hc.am3⟩) ps pt pub

theorem jointVerify_ct :
    ConstantTime isa
      (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256v.combConsts)).pre
      (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256v.combConsts)).pub
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p256v publicJoint (jointDouble publicJoint.K)).inline := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact jointVerify_p256_public_ct hL hT hI hO _ _ _ _ _ _ (preG_of (impliesG.pre _ pre₁))
    (preG_of (impliesG.pre _ pre₂)) (jointPublic_of_spec pub) e₁ e₂

theorem jointVerify_adx_ct :
    ConstantTime isa
      (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256v.combConsts)).pre
      (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256v.combConsts)).pub
      (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p256vx publicJointAdx (jointDouble publicJointAdx.K)).inline := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  exact jointVerify_p256_adx_public_ct hL hT hI hO _ _ _ _ _ _
    (show VPre p256vx s₁ from { preG_of (impliesG.pre _ pre₁) with })
    (show VPre p256vx s₂ from { preG_of (impliesG.pre _ pre₂) with })
    (show JointPublic p256vx p256GTab s₁ s₂ from { jointPublic_of_spec pub with }) e₁ e₂

end
end VG.Proof.Ecdsa.Verify.X86_64
end

end

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.Ecdsa.Verify.X86_64
open VG.Impl.P256.X86_64 (p256v)

section
variable (hL : Weierstrass.Law Spec.P256.curve)
    (hT : Weierstrass.CombOkW Spec.P256.curve 9 1 Impl.P256.p256G9 Impl.P256.p256G9Start)
    (hI : Weierstrass.X86_64.InvSounds)
    (hO : Weierstrass.PrimeOrder Spec.P256.curve)
include hL hT hI hO

theorem jointVerify_verified : Verified X86_64.target jointVerifyP256
    (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256v.combConsts) 8) :=
  Verified.of_inline (k₀ := verifyGK₀) jointVerifyP256_inlineOk (fun s hs => jointVerify_x86 hL hT hI hO s (impliesG.pre _ hs))
    (jointVerify_ct hL hT hI hO) impliesG8 (fun _ h => Sig.clear_of_pre_consts h) (fun _ _ _ _ _ hp => hp)
    fun s₁ s₂ h₁ h₂ hp => (impliesG.pub s₁ s₂ (Sig.pre_stack0 h₁) (Sig.pre_stack0 h₂) hp).1

theorem jointVerify_verified_adx : Verified X86_64.target jointVerifyP256Adx
    (Spec.Ecdsa.P256.inst.verifyContract (X86_64.abi.withConsts p256v.combConsts) 8) :=
  Verified.of_inline (k₀ := verifyGK₀) jointVerifyP256Adx_inlineOk (fun s hs => jointVerify_x86_adx hL hT hI hO s (impliesG.pre _ hs))
    (jointVerify_adx_ct hL hT hI hO) impliesG8 (fun _ h => Sig.clear_of_pre_consts h) (fun _ _ _ _ _ hp => hp)
    fun s₁ s₂ h₁ h₂ hp => (impliesG.pub s₁ s₂ (Sig.pre_stack0 h₁) (Sig.pre_stack0 h₂) hp).1

/-- `vg_ecdsa_p256_verify`, taking the hash function's output: `jointVerify_verified`,
run on the `len` bytes of the hash (`verifyHash_verified_cons`). -/
theorem verifyHash_verified : Verified X86_64.target
    (Impl.Ecdsa.X86_64.VerifyHash.verifyHash Spec.Ecdsa.P256.inst.curve.len false jointVerifyP256)
    (Spec.Ecdsa.P256.inst.verifyHashContract (X86_64.abi.withConsts p256v.combConsts) 96) :=
  Hash.verifyHash_verified_cons Proof.Ecdsa.Verify.p256_len (by decide) (jointVerify_verified hL hT hI hO)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by taint_decide)
    (Hash.hashSat_cons (by decide) satG_spec8 (by decide) fun r hr => by
      simp only [satStateG, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

/-- `vg_ecdsa_p256_verify_adx`, taking the hash function's output: `jointVerify_verified_adx`,
run on the `len` bytes of the hash (`verifyHash_verified_cons`). -/
theorem verifyHash_verified_adx : Verified X86_64.target
    (Impl.Ecdsa.X86_64.VerifyHash.verifyHash Spec.Ecdsa.P256.inst.curve.len false jointVerifyP256Adx)
    (Spec.Ecdsa.P256.inst.verifyHashContract (X86_64.abi.withConsts p256v.combConsts) 96) :=
  Hash.verifyHash_verified_cons Proof.Ecdsa.Verify.p256_len (by decide) (jointVerify_verified_adx hL hT hI hO)
    (Code.all_of_allInstrs (by lit_decide)) (by lit_decide) (by taint_decide)
    (Hash.hashSat_cons (by decide) satG_spec8 (by decide) fun r hr => by
      simp only [satStateG, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact Region.disjoint_of_sep (by decide))

end
end VG.Proof.Ecdsa.Verify.X86_64
