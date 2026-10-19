module

public import VerifiedGarbage.Impl.CmacTripleDes.AArch64.Round
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.CmacTripleDes.AArch64.Round
import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
meta import VerifiedGarbage.Proof.CmacTripleDes.IndexLit
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

/-! # The key schedule's code as a literal, for kernel-evaluated checks

Evaluated once, here: the checks of `Keys.lean` and the literal of `init`
(`Lit.lean`), which runs it, read it. -/

@[expose] public section

namespace VG

materialize_value Impl.CmacTripleDes.AArch64.roundKeys

theorem Proof.CmacTripleDes.AArch64.roundKeys_eq :
    Impl.CmacTripleDes.AArch64.roundKeys = Impl.CmacTripleDes.AArch64.roundKeys.lit :=
  Impl.CmacTripleDes.AArch64.roundKeys.lit_eq

end VG
