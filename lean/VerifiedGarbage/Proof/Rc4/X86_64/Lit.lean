module

public import VerifiedGarbage.Impl.Rc4.X86_64
meta import VerifiedGarbage.Impl.Rc4.X86_64
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! Literal code keeps unrolled table scans cheap for kernel-evaluated audits. -/

@[expose] public section

namespace VG.Impl.Rc4.X86_64
materialize_value lookup
materialize_value replace
materialize_value scheduleStep
materialize_value applyStep
materialize_code init
materialize_code apply
end VG.Impl.Rc4.X86_64
