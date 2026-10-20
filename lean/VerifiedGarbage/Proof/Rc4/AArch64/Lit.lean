module

public import VerifiedGarbage.Impl.Rc4.AArch64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Rc4.AArch64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! Literal code keeps the unrolled groups cheap for kernel-evaluated audits. -/

@[expose] public section

namespace VG.Impl.Rc4.AArch64
materialize_code applyRest
materialize_code apply
materialize_code init
end VG.Impl.Rc4.AArch64
