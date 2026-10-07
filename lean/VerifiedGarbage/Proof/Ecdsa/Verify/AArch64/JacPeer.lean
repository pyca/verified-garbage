import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPublic

/-! The verifier's initialized peer point is determined by its public key buffer. -/
namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)

theorem Mid.peer_rep {c : Cfg} (hc : CfgOk c) (hC : Law c.C)
    {s₀ a : State} {base : Addr} {g : Reg → BitVec 64} (h : Mid c s₀ base g a) :
    Rep c.C (tmv c.C c.n base a (c.sl PX)) (tmv c.C c.n base a (c.sl PY))
      (tmv c.C c.n base a (c.sl ONEP))
      (peerPt c (s₀.mem (s₀.gpr .x0)=4) (keyX c s₀) (keyY c s₀)) := by
  rw [onep_tmv hc h.fixed]
  exact peerPt_rep hC _ _ _ h.px h.py

theorem JacPublic.peerPoint {c : Cfg} {s t : State} (h : JacPublic c s t) :
    peerPt c (s.mem (s.gpr .x0)=4) (keyX c s) (keyY c s) =
      peerPt c (t.mem (t.gpr .x0)=4) (keyX c t) (keyY c t) := by
  obtain ⟨tag,x,y⟩ := publicKey_congr h.key
  rw [tag,x,y]

end VG.Proof.Ecdsa.Verify.AArch64
