module

public import VerifiedGarbage.Impl.Rc4.RISCV64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Rc4.RISCV64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! Literal code keeps the unrolled table scans cheap for kernel-evaluated audits. -/

@[expose] public section

namespace VG.Impl.Rc4.RISCV64
materialize_value lookup
materialize_value replace
materialize_value scheduleStep
materialize_value applyStep
materialize_code init
materialize_code apply
end VG.Impl.Rc4.RISCV64
