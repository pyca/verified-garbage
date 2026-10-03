import VerifiedGarbage.Impl.Rc4.Arm
import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! Literal code keeps unrolled table scans cheap for kernel-evaluated audits. -/
namespace VG.Impl.Rc4.Arm
materialize_value lookup
materialize_value replace
materialize_value scheduleStep
materialize_value applyStep
materialize_code init
materialize_code apply
end VG.Impl.Rc4.Arm
