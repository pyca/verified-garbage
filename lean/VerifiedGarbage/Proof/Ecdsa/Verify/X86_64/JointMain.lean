import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTail

/-! End-to-end correctness of public Jacobian joint verification. -/
namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open VG.Proof.Ecdsa.X86_64 VG.Proof.Ecdh.X86_64 Spec.Weierstrass
open VG.Impl.Ecdh.X86_64 (PX PY)

theorem jointVerify_ok {c : Cfg} {j : Joint.Cfg} {double : Prog isa}
    (hc : CfgOk c) (hC : Law c.C)
    (hpub : c.pubVerify=true) (hnp : c.C.n<c.C.p) (hpn : c.C.p≤2*c.C.n)
    {s₀ : State} (hp : VPre c s₀)
    (hpoints : ∀ {s : State} {g : Reg → BitVec 64} (_h : Mid c s₀ (s₀.gpr .rcx) g s)
      {Q : Point c.C}, onCurve c.C Q=true →
      Rep c.C (tmv c.C c.n (s₀.gpr .rcx) s (c.sl PX))
        (tmv c.C c.n (s₀.gpr .rcx) s (c.sl PY)) (tmv c.C c.n (s₀.gpr .rcx) s (c.sl ONEP)) Q →
      WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointPoints c j double) s (JointPointsPost c s₀ s g Q)) :
    WP isa (Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify c j double) s₀ fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s₀.gpr r) ∧ VPost c s₀ t := by
  unfold Impl.Ecdsa.Verify.X86_64.Cfg.jointVerify
  refine front_ok hc hp fun g s₁ hg hF => mid_ok hc hF fun s₂ hM => ?_
  have one := (consts_tmv hc hM.fixed).2.2
  let Q := peerPt c (s₀.mem (s₀.gpr .rdi)=4) (keyX c s₀) (keyY c s₀)
  have hQ : onCurve c.C Q=true := peerPt_onCurve hc _ _ _
  have hRep : Rep c.C (tmv c.C c.n (s₀.gpr .rcx) s₂ (c.sl PX))
      (tmv c.C c.n (s₀.gpr .rcx) s₂ (c.sl PY)) (tmv c.C c.n (s₀.gpr .rcx) s₂ (c.sl ONEP)) Q := by
    rw [one]
    exact peerPt_rep hC _ _ _ hM.px hM.py
  apply WP.seq
  refine WP.mono (hpoints hM hQ hRep) fun s₃ hP => ?_
  refine WP.mono (jointTail_ok hc hC hpub hnp hpn hM hP.input hP.point) fun t ⟨saved,post⟩ => ?_
  exact ⟨fun r hr => (saved r hr).trans (hg r hr),post⟩

end VG.Proof.Ecdsa.Verify.X86_64
