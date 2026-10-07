import VerifiedGarbage.Impl.P256.X86_64.Joint
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointPrepFields

/-! The baseline and ADX layouts of the two scalar recoders. -/
namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

theorem joint_prep_layout : JointPrepLayout publicJoint 8192
    (Impl.Ecdsa.X86_64.p256.sl Impl.Ecdsa.Verify.X86_64.U)
    (Impl.Ecdsa.X86_64.p256.sl Impl.Ecdsa.Verify.X86_64.V) := by
  constructor <;> decide

theorem joint_adx_prep_layout : JointPrepLayout publicJointAdx 8192
    (Impl.Ecdsa.X86_64.p256x.sl Impl.Ecdsa.Verify.X86_64.U)
    (Impl.Ecdsa.X86_64.p256x.sl Impl.Ecdsa.Verify.X86_64.V) := by
  constructor <;> decide

end VG.Proof.P256.X86_64
