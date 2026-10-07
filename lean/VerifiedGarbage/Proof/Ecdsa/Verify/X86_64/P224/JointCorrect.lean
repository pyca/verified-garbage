import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointMain
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P224.JointChecks

/-! Joint verification over P-224 satisfies the functional specification. -/
namespace VG.Proof.Ecdsa.Verify.X86_64.P224
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P224.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.P224.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64

theorem jointVerify_p224_ok (hL : Law Spec.P224.curve)
    (hT : CombOkW Spec.P224.curve 7 37 Impl.P224.p224Comb7 Impl.P224.p224Comb7Start)
    (hI : InvSounds) {s : State} (hp : VPre p224v s) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify p224v publicJoint (Joint.jacDouble publicJoint.K)) s
      fun t => (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p224v s t := by
  have hc := p224v_ok hI
  refine jointVerify_ok hc hL rfl (by decide +kernel) (by decide +kernel) hp ?_
  intro a g hM Q hQ hRep
  exact jointPoints_ok hc hL (p224v_tbls hT) rfl rfl rfl rfl hc.am3 (by decide +kernel)
    joint_add_layout joint_init_layout joint_prep_layout joint_frame_layout (joint_doubler hc hL)
    hp hM hQ hRep

end VG.Proof.Ecdsa.Verify.X86_64.P224
