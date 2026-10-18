module
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointBoundaryTiming
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.JointChecks
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

theorem verify_public_ct (hc : CfgOk p521) (hC : Law p521.C) (hO : PrimeOrder p521.C)
 (hn : 17≤p521.C.n) (hT : CombOkW p521.C 7 83 p521.tbl p521.start) :
 ConstantTime isa (VPre p521) (JacPublic p521) P521Joint.verify := by
 apply jointVerify_ct_of_points hc before_ct
 · intro s₀ t₀ hs ht
   exact points_relCT hc hC hO hn hT prep7_checks prep5_checks window_checks mixed_checks hs ht
 · exact tail_ct
end VG.Proof.Ecdsa.Verify.AArch64.P521.Joint
