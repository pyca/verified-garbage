module

public import VerifiedGarbage.Impl.Rc4.X86
meta import VerifiedGarbage.Impl.Rc4.X86
public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-! Literal code keeps unrolled table scans cheap for kernel-evaluated audits. -/

@[expose] public section

namespace VG.Impl.Rc4.X86
materialize_value lookup
materialize_value replace
materialize_value scheduleStep
materialize_value applyStep
materialize_code init
materialize_code apply
end VG.Impl.Rc4.X86
