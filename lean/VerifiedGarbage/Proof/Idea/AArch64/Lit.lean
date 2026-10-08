import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Impl.Idea.AArch64

/-! # Literal IDEA programs for kernel-evaluated checks (AArch64) -/

namespace VG

materialize_code Impl.Idea.AArch64.expandKey
materialize_code Impl.Idea.AArch64.invertKey
materialize_code Impl.Idea.AArch64.ecb

end VG
