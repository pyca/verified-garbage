module
public import VerifiedGarbage.Impl.AArch64Instrs
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P384Joint
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Front
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
/-- The interleaved multiplication retains all validation and the original public postcondition. -/
theorem verify_ok (hc : CfgOk p384) (hC : Law p384.C) (hO : PrimeOrder p384.C)
 (hn : 17≤p384.C.n) (hT : CombOkW p384.C 9 1 P384Joint.p384v.tbl P384Joint.p384v.start)
 (hD : ∀ base, Weierstrass.AArch64.DblSpec P384Joint.K p384.C base 8192 P384Joint.double P384Joint.K.R
   P384Joint.K.D (Weierstrass.AArch64.dblVR P384Joint.K))
 {s : State} (hp : VPreT p384 "VG_P384_GTAB" P384Joint.p384v.combWords s) :
 WP isa P384Joint.verify s fun t=>
  (∀r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p384 s t :=
 verify_of_joint hc hC P384Joint.points P384Joint.verify rfl
  (fun {_} {_} {_} {_} hm ht {_} hP hr=>points_ok hc hC hO hn hT hD hm ht hP hr) hp
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
