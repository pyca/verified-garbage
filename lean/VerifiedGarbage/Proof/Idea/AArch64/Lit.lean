module

import VerifiedGarbage.Proof.Idea.KeyLit
public import VerifiedGarbage.Impl.Idea.AArch64
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Idea.KeyLit
meta import VerifiedGarbage.Impl.Idea.AArch64
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit

/-! # Literal IDEA programs for kernel-evaluated checks (AArch64) -/

@[expose] public section

namespace VG

materialize_code Impl.Idea.AArch64.expandKey
materialize_code Impl.Idea.AArch64.invertKey
materialize_code Impl.Idea.AArch64.ecb

end VG
