import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointMain
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointAbi

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64

theorem jointVerify_ok (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    {s : State} (h : VPre p256 s) :
    WP isa P256Joint.verify s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p256 s t :=
  verify_of_joint (p256_ok hI) hL P256Joint.points P256Joint.verify rfl
    (by
      intro s₀ base g s hm ht P hp hr
      exact jointPoints_ok (p256_ok hI) hL hT hm ht hp hr) h

theorem jointVerify_a64 (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (s : State) (hs : verifyAArch64.pre s) :
    ∃ t s',Exec isa P256Joint.verify s t s' ∧ abiPreserved s s' ∧ verifyAArch64.post s s' :=
  jointVerify_a64_of_wp (fun _ hp => jointVerify_ok hL hI hT hp) s hs

end VG.Proof.Ecdsa.Verify.AArch64
