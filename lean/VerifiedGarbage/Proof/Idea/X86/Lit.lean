module

public import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Idea.KeyLit32
meta import VerifiedGarbage.Proof.Idea.KeyLit32
public import VerifiedGarbage.Impl.Idea.X86
meta import VerifiedGarbage.Impl.Idea.X86
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs

/-! # Literal IDEA programs for kernel-evaluated checks (x86) -/

@[expose] public section

namespace VG

materialize_code Impl.Idea.X86.expandKey
materialize_code Impl.Idea.X86.invertKey
materialize_code Impl.Idea.X86.ecb

end VG
