import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointPrefix
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointPrepTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPeer

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open VG.Proof.Ecdh.AArch64 Spec.Weierstrass

/-- The original public verifier relation determines both joint scalars and the peer. -/
theorem jointBoundary_input (hc : CfgOk p256) (hC : Law p256.C)
    {s₀ t₀ s t : State} (h : JointBoundary p256 s₀ t₀ s t) :
    JacWinPublic p256 (s₀.gpr .x3)
      (peerPt p256 (s₀.mem (s₀.gpr .x0)=4) (keyX p256 s₀) (keyY p256 s₀))
      (publicV p256 s₀) s t ∧
    sv p256 (s₀.gpr .x3) s U=publicU p256 s₀ ∧
    sv p256 (s₀.gpr .x3) t U=publicU p256 s₀ := by
  obtain ⟨pub,⟨g₁,m₁⟩,⟨g₂,m₂⟩,sp⟩ := h
  have peer := mid_peer_public pub m₁ m₂
  refine ⟨⟨⟨m₁.scr,⟨g₁,m₁.fixed⟩,m₁.px_lt,m₁.py_lt,m₁.peer_rep hc hC,mid_publicV m₁⟩,
    ⟨m₂.scr,⟨g₂,m₂.fixed⟩,m₂.px_lt,m₂.py_lt,?_,(mid_publicV m₂).trans pub.v.symm⟩,
    sp,peer.1,peer.2⟩,mid_publicU m₁,(mid_publicU m₂).trans pub.u.symm⟩
  rw [pub.peerPoint]
  exact m₂.peer_rep hc hC

end VG.Proof.Ecdsa.Verify.AArch64
