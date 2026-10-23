module

import VerifiedGarbage.Proof.Idea.KeyLit
public import VerifiedGarbage.Impl.Idea.PPC64LE
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Idea.KeyLit
meta import VerifiedGarbage.Impl.Idea.PPC64LE
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Lit

/-! # Literal IDEA programs for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.Idea.PPC64LE.expandKey
materialize_code Impl.Idea.PPC64LE.invertKey
materialize_code Impl.Idea.PPC64LE.ecb

end VG
