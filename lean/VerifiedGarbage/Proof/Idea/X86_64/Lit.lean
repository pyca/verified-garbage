module

public import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Idea.KeyLit
meta import VerifiedGarbage.Proof.Idea.KeyLit
public import VerifiedGarbage.Impl.Idea.X86_64
meta import VerifiedGarbage.Impl.Idea.X86_64
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Literal IDEA programs for kernel-evaluated checks -/

@[expose] public section

namespace VG

materialize_code Impl.Idea.X86_64.expandKey
materialize_code Impl.Idea.X86_64.invertKey
materialize_code Impl.Idea.X86_64.ecb

end VG
