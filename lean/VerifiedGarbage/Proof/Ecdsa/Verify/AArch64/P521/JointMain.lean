module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointPoints
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
/-- The interleaved multiplication retains all validation and the original public postcondition. -/
theorem verify_ok (hc : CfgOk p521) (hC : Law p521.C) (hO : PrimeOrder p521.C)
 (hn : 17≤p521.C.n) (hT : CombOkW p521.C 7 83 p521.tbl p521.start)
 {s : State} (hp : VPre p521 s) :
 WP isa P521Joint.verify s fun t=>
  (∀r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p521 s t :=
 verify_of_joint hc hC P521Joint.points P521Joint.verify rfl
  (fun {_} {_} {_} {_} hm ht {_} hP hr=>points_ok hc hC hO hn hT hm ht hP hr) hp
end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
