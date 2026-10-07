import VerifiedGarbage.Proof.P256.X86_64.JointLayout
import VerifiedGarbage.Proof.P256.X86_64.JointFixedTiming
import VerifiedGarbage.Proof.P256.X86_64.NafCacheTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointCachedDigitTiming
import VerifiedGarbage.Proof.Weierstrass.X86_64.JointFixedDigitTiming

/-! Taint checks of P-256's baseline and ADX digit additions in the joint loop. -/
namespace VG.Proof.P256.X86_64
open VG VG.X86_64 VG.Impl.P256.X86_64 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86_64
open VG.Proof.Mont VG.Proof.Mont.X86_64 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86_64
open Spec.Weierstrass

theorem joint_cached_checks : JointCachedChecks publicJoint := by
  refine ⟨?_,nafSignedCachedEntry_ct,nafCachedJac_checks,?_⟩
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_adx_cached_checks : JointCachedChecks publicJointAdx := by
  refine ⟨?_,nafSignedCachedEntry_adx_ct,nafCachedJac_adx_checks,?_⟩
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
      (fun _ _ _ _ h => h) (by taint_decide)
  · exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
      (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_fixed_checks : JointFixedChecks publicJoint := by
  refine ⟨?_,jointFixedEntry_ct,nafMixedJac_checks,joint_cached_checks.copy⟩
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_adx_fixed_checks : JointFixedChecks publicJointAdx := by
  refine ⟨?_,jointFixedEntry_adx_ct,nafMixedJac_adx_checks,joint_adx_cached_checks.copy⟩
  exact VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rbx])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.P256.X86_64
