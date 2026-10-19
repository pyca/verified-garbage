module

import VerifiedGarbage.Proof.Idea.KeyLit32
meta import VerifiedGarbage.Proof.Idea.KeyLit32
public import VerifiedGarbage.Impl.Idea.X86
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Idea.X86
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.X86.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-! # Literal IDEA programs for kernel-evaluated checks (x86) -/

@[expose] public section

namespace VG

materialize_code Impl.Idea.X86.expandKey
materialize_code Impl.Idea.X86.invertKey
materialize_code Impl.Idea.X86.ecb

end VG
