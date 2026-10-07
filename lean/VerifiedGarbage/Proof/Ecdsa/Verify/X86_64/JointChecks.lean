import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPointsTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.LitAdx

/-! Concrete timing checks for baseline and ADX public joint verification. -/
namespace VG.Proof.Ecdsa.Verify.X86_64
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P256.X86_64
open VG.Proof.P256.X86_64 VG.Proof.Weierstrass.X86_64

theorem joint_mul_checks : JointMulChecks p256 publicJoint :=
  ⟨joint_cached_checks,joint_fixed_checks,doubleHalfPublic_ct,nafTable_checks,nafCacheTable_ct,
    joint_infinity_ct,fastGenerator_checks,fastPeer_checks⟩

theorem joint_adx_mul_checks : JointMulChecks p256x publicJointAdx :=
  ⟨joint_adx_cached_checks,joint_adx_fixed_checks,doubleHalfPublic_adx_ct,nafTable_adx_checks,
    nafCacheTable_adx_ct,joint_adx_infinity_ct,fastGenerator_adx_checks,fastPeer_adx_checks⟩

theorem joint_before_ct : ConstantTime isa (fun _ => True)
    (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])) (jointPrefix p256) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_adx_before_ct : ConstantTime isa (fun _ => True)
    (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])) (jointPrefix p256x) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_after_ct : ScratchCT (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p256) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_adx_after_ct : ScratchCT (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p256x) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.Ecdsa.Verify.X86_64
