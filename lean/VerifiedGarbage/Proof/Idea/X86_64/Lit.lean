import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Idea.KeyLit
import VerifiedGarbage.Impl.Idea.X86_64

/-! # Literal IDEA programs for kernel-evaluated checks -/

namespace VG

materialize_code Impl.Idea.X86_64.expandKey
materialize_code Impl.Idea.X86_64.invertKey
materialize_code Impl.Idea.X86_64.ecb

end VG
