module

import VerifiedGarbage.Proof.Idea.KeyLit
public import VerifiedGarbage.Impl.Idea.X86_64
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Idea.KeyLit
meta import VerifiedGarbage.Impl.Idea.X86_64
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! # Literal IDEA programs for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.Idea.X86_64.expandKey
materialize_code Impl.Idea.X86_64.invertKey
materialize_code Impl.Idea.X86_64.ecb

end VG
