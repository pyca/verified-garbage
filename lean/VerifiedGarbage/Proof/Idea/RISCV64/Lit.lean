module

public import VerifiedGarbage.Impl.Idea.RISCV64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Idea.RISCV64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.RISCV64.Lit

/-! # Literal IDEA programs for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.Idea.RISCV64.expandKey
materialize_code Impl.Idea.RISCV64.invertKey
materialize_code Impl.Idea.RISCV64.ecb

end VG
