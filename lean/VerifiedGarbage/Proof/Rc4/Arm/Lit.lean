module

public import VerifiedGarbage.Impl.Rc4.Arm
meta import VerifiedGarbage.Impl.Rc4.Arm
public import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-! Literal code keeps unrolled table scans cheap for kernel-evaluated audits. -/

@[expose] public section

namespace VG.Impl.Rc4.Arm
materialize_value lookup
materialize_value replace
materialize_value scheduleStep
materialize_value applyStep
materialize_code init
materialize_code apply
end VG.Impl.Rc4.Arm
