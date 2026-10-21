module

import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointMain
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointChecks
public import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.Main
import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.P256.X86_64.JointFrame
import VerifiedGarbage.Proof.P256.X86_64.JointInitLayout
import VerifiedGarbage.Proof.P256.X86_64.JointPrep
import VerifiedGarbage.Proof.P256.X86_64.JointLayout
import VerifiedGarbage.Proof.Ecdsa.X86_64.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointContract

/-! Baseline and ADX joint verification satisfy the existing functional specification. -/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P256.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.P256.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

section
variable (hL : Law Spec.P256.curve)
    (hT : CombOkW Spec.P256.curve 9 1 Impl.P256.p256G9 Impl.P256.p256G9Start)
    (hI : InvSounds) (hO : PrimeOrder Spec.P256.curve)

include hL hT hI hO

theorem jointVerify_p256_ok {s : State} (hp : VPre p256v s) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p256v publicJoint (jointDouble publicJoint.K)).inline s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p256v s t := by
  have hc := p256v_ok hI
  refine jointVerify_ok hc hL rfl (by decide +kernel) (by decide +kernel) hp ?_
  intro a g hM Q hQ hRep
  exact jointPoints_ok hc hL (.ofGTab rfl hT (by decide) (by decide) rfl) rfl hc.am3 (by decide +kernel)
    joint_add_layout joint_init_layout joint_prep_layout joint_frame_layout (joint_doubler hc hL)
    (fun _ => ⟨hO,by decide⟩) hp hM hQ hRep

theorem jointVerify_p256_adx_ok {s : State} (hp : VPre p256vx s) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p256vx publicJointAdx (jointDouble publicJointAdx.K)).inline s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p256vx s t := by
  have hc := p256vx_ok hI
  refine jointVerify_ok hc hL rfl (by decide +kernel) (by decide +kernel) hp ?_
  intro a g hM Q hQ hRep
  exact jointPoints_ok hc hL (.ofGTab rfl hT (by decide) (by decide) rfl) rfl hc.am3 (by decide +kernel)
    joint_adx_add_layout joint_adx_init_layout joint_adx_prep_layout joint_adx_frame_layout
    (joint_adx_doubler hc hL) (fun _ => ⟨hO,by decide⟩) hp hM hQ hRep

end
end VG.Proof.Ecdsa.Verify.X86_64
