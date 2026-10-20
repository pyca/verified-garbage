module

import VerifiedGarbage.Proof.Idea.KeyLit32
public import VerifiedGarbage.Impl.Idea.X86
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Idea.KeyLit32
meta import VerifiedGarbage.Impl.Idea.X86
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit

/-! # Literal IDEA programs for kernel-evaluated checks (x86) -/

@[expose] public section

namespace VG

materialize_code Impl.Idea.X86.expandKey
materialize_code Impl.Idea.X86.invertKey
materialize_code Impl.Idea.X86.ecb

end VG
