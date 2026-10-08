import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointMain
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P521.JointChecks

/-! Baseline and ADX joint verification over P-521 satisfy the functional specification. -/
namespace VG.Proof.Ecdsa.Verify.X86_64.P521
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P521.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.P521.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64.P521 (p521_ok p521x_ok p521_tbls p521x_tbls)

section
variable (hL : Law Spec.P521.curve)
    (hT : CombOkW Spec.P521.curve 7 83 Impl.P521.p521Comb7 Impl.P521.p521Comb7Start)
    (hI : InvSounds)

include hL hT hI

theorem jointVerify_p521_ok {s : State} (hp : VPre p521 s) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p521 publicJoint (Joint.jacDouble publicJoint.K)).inline s
      fun t => (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p521 s t := by
  have hc := p521_ok hI
  refine jointVerify_ok hc hL rfl (by decide +kernel) (by decide +kernel) hp ?_
  intro a g hM Q hQ hRep
  exact jointPoints_ok hc hL (p521_tbls hT) rfl rfl rfl rfl hc.am3 (by decide +kernel)
    joint_add_layout joint_init_layout joint_prep_layout joint_frame_layout (joint_doubler hc hL)
    hp hM hQ hRep

theorem jointVerify_p521_adx_ok {s : State} (hp : VPre p521x s) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p521x publicJointAdx
      (Joint.jacDouble publicJointAdx.K)).inline s
      fun t => (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p521x s t := by
  have hc := p521x_ok hI
  refine jointVerify_ok hc hL rfl (by decide +kernel) (by decide +kernel) hp ?_
  intro a g hM Q hQ hRep
  exact jointPoints_ok hc hL (p521x_tbls hT) rfl rfl rfl rfl hc.am3 (by decide +kernel)
    joint_adx_add_layout joint_adx_init_layout joint_adx_prep_layout joint_adx_frame_layout
    (joint_adx_doubler hc hL) hp hM hQ hRep

end
end VG.Proof.Ecdsa.Verify.X86_64.P521
