import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointMain
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointChecks
import VerifiedGarbage.Proof.Ecdsa.X86_64.VerifiedAdx

/-! Baseline and ADX joint verification satisfy the existing functional specification. -/
namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P256.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.P256.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

section
variable (hL : Law Spec.P256.curve)
    (hT : CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (hI : InvSounds)

include hL hT hI

theorem jointVerify_p256_ok {s : State} (hp : VPre p256 s) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p256 publicJoint (jointDouble publicJoint.K)) s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p256 s t := by
  have hc := p256_ok hI
  refine jointVerify_ok hc hL rfl (by decide +kernel) (by decide +kernel) hp ?_
  intro a g hM Q hQ hRep
  exact jointPoints_ok hc hL (p256_tbls hL hT) rfl rfl rfl rfl hc.am3 (by decide +kernel)
    joint_add_layout joint_init_layout joint_prep_layout joint_frame_layout (joint_doubler hc hL) hp hM hQ hRep

theorem jointVerify_p256_adx_ok {s : State} (hp : VPre p256x s) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p256x publicJointAdx (jointDouble publicJointAdx.K)) s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p256x s t := by
  have hc := p256x_ok hI
  refine jointVerify_ok hc hL rfl (by decide +kernel) (by decide +kernel) hp ?_
  intro a g hM Q hQ hRep
  exact jointPoints_ok hc hL (p256_tbls hL hT) rfl rfl rfl rfl hc.am3 (by decide +kernel)
    joint_adx_add_layout joint_adx_init_layout joint_adx_prep_layout joint_adx_frame_layout
    (joint_adx_doubler hc hL) hp hM hQ hRep

end
end VG.Proof.Ecdsa.Verify.X86_64
