module

import VerifiedGarbage.Proof.Idea.KeyLit
meta import VerifiedGarbage.Proof.Idea.KeyLit
public import VerifiedGarbage.Impl.Idea.AArch64
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Idea.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

/-! # Literal IDEA programs for kernel-evaluated checks (AArch64) -/

@[expose] public section

namespace VG

materialize_code Impl.Idea.AArch64.expandKey
materialize_code Impl.Idea.AArch64.invertKey
materialize_code Impl.Idea.AArch64.ecb

end VG
