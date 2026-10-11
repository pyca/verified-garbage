import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Idea.KeyLit32
import VerifiedGarbage.Impl.Idea.X86

/-! # Literal IDEA programs for kernel-evaluated checks (x86) -/

namespace VG

materialize_code Impl.Idea.X86.expandKey
materialize_code Impl.Idea.X86.invertKey
materialize_code Impl.Idea.X86.ecb

end VG
