import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointMain
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P384.JointChecks

/-! Baseline and ADX joint verification over P-384 satisfy the functional specification. -/
namespace VG.Proof.Ecdsa.Verify.X86_64.P384
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P384.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.P384.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

section
variable (hL : Law Spec.P384.curve)
    (hT : CombOkW Spec.P384.curve 7 55 Impl.P384.p384Comb7 Impl.P384.p384Comb7Start)
    (hI : InvSounds)

include hL hT hI

theorem jointVerify_p384_ok {s : State} (hp : VPre p384v s) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p384v publicJoint (Joint.jacDouble publicJoint.K)).inline s
      fun t => (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p384v s t := by
  have hc := p384v_ok hI
  refine jointVerify_ok hc hL rfl (by decide +kernel) (by decide +kernel) hp ?_
  intro a g hM Q hQ hRep
  exact jointPoints_ok hc hL (p384v_tbls hT) rfl rfl rfl rfl hc.am3 (by decide +kernel)
    joint_add_layout joint_init_layout joint_prep_layout joint_frame_layout (joint_doubler hc hL)
    hp hM hQ hRep

theorem jointVerify_p384_adx_ok {s : State} (hp : VPre p384vx s) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p384vx publicJointAdx
      (Joint.jacDouble publicJointAdx.K)).inline s
      fun t => (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p384vx s t := by
  have hc := p384vx_ok hI
  refine jointVerify_ok hc hL rfl (by decide +kernel) (by decide +kernel) hp ?_
  intro a g hM Q hQ hRep
  exact jointPoints_ok hc hL (p384vx_tbls hT) rfl rfl rfl rfl hc.am3 (by decide +kernel)
    joint_adx_add_layout joint_adx_init_layout joint_adx_prep_layout joint_adx_frame_layout
    (joint_adx_doubler hc hL) hp hM hQ hRep

end
end VG.Proof.Ecdsa.Verify.X86_64.P384
