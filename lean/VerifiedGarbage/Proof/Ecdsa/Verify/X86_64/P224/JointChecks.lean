import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointPointsTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.JointTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.X86_64.P224.JointContract
import VerifiedGarbage.Proof.P224.X86_64.JointTiming
import VerifiedGarbage.Proof.P224.X86_64.NafTableTiming
import VerifiedGarbage.Proof.P224.X86_64.JointLayout
import VerifiedGarbage.Proof.P224.X86_64.JointFrame

/-! Concrete timing checks and the doubler of P-224's joint verification. -/
namespace VG.Proof.Ecdsa.Verify.X86_64.P224
open VG VG.X86_64 VG.Impl.Ecdsa.X86_64 VG.Impl.P224.X86_64 VG.Impl.Weierstrass.X86_64
open VG.Proof.P224.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Ecdsa.X86_64 VG.Proof.Mont

theorem joint_mul_checks : JointMulChecks p224v publicJoint :=
  ⟨joint_cached_checks,joint_fixed_checks,nafTable_checks,nafCacheTable_ct,
    joint_infinity_ct,joint_counter_ct,fastGenerator_checks,fastPeer_checks⟩

theorem joint_doubler (hc : CfgOk p224v) (hC : Weierstrass.Law p224v.C) :
    JointDoubler publicJoint p224v.C size (Joint.jacDouble publicJoint.K) :=
  jacDouble_doubler joint_add_layout (Weierstrass.unitMod_pow_two hc.p_odd _) hC hc.am3
    jointDouble_ct joint_cached_checks.copy

theorem joint_before_ct : ConstantTime isa (fun _ => True)
    (X86_64.Taint.Agree (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])) (jointPrefix p224v) :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi,.rsi,.rdx,.rcx])
    (fun _ _ _ _ h => h) (by taint_decide)

theorem joint_after_ct : ScratchCT (Impl.Ecdsa.Verify.X86_64.Cfg.jointTail p224v).inline :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.rdi])
    (fun _ _ _ _ h => h) (by taint_decide)

end VG.Proof.Ecdsa.Verify.X86_64.P224
