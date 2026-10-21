module
public import VerifiedGarbage.Proof.Weierstrass.PrimeOrder
public import VerifiedGarbage.Impl.AArch64Instrs
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.P384Joint
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPrefix
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.P256Bounds
public import VerifiedGarbage.Proof.Weierstrass.AArch64.WinJStep
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Front
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointBoundaryTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P384.JointTopTiming
@[expose] public section
namespace VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

theorem verify_public_ct (hc : CfgOk p384) (hC : Law p384.C) (hO : PrimeOrder p384.C)
 (hn : 17≤p384.C.n) (hT : CombOkW p384.C 9 1 P384Joint.p384v.tbl P384Joint.p384v.start)
 (hD : ∀ base, VG.Proof.Weierstrass.AArch64.DblSpec P384Joint.K p384.C base 8192 P384Joint.double
   P384Joint.K.R P384Joint.K.D (VG.Proof.Weierstrass.AArch64.dblVR P384Joint.K)) :
 ConstantTime isa (VPreT p384 "VG_P384_GTAB" P384Joint.p384v.combWords) (JacPublicT p384 "VG_P384_GTAB")
  P384Joint.verify := by
 apply jointVerify_ct_of_points hc before_ct
 · intro s₀ t₀ hs ht
   exact points_relCT hc hC hO hn hT prep9_checks prep5_checks window_checks hD double_ct mixed_checks hs ht
 · exact tail_ct
end VG.Proof.Ecdsa.Verify.AArch64.P384.Joint
