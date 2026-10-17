module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Idea.KeyLit
meta import VerifiedGarbage.Proof.Idea.KeyLit
public import VerifiedGarbage.Impl.Idea.AArch64
meta import VerifiedGarbage.Impl.Idea.AArch64

/-! # Literal IDEA programs for kernel-evaluated checks (AArch64) -/

@[expose] public section

namespace VG

materialize_code Impl.Idea.AArch64.expandKey
materialize_code Impl.Idea.AArch64.invertKey
materialize_code Impl.Idea.AArch64.ecb

end VG
