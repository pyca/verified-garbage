module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Idea.KeyLit
meta import VerifiedGarbage.Proof.Idea.KeyLit
public import VerifiedGarbage.Impl.Idea.AArch64
meta import VerifiedGarbage.Impl.Idea.AArch64
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Literal IDEA programs for kernel-evaluated checks (AArch64) -/

@[expose] public section

namespace VG

materialize_code Impl.Idea.AArch64.expandKey
materialize_code Impl.Idea.AArch64.invertKey
materialize_code Impl.Idea.AArch64.ecb

end VG
