module

public import VerifiedGarbage.Impl.Argon2.AArch64.ClearBlock
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Argon2.AArch64.ClearBlock
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Spec.Argon2
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Spec.Argon2
meta import VerifiedGarbage.TCB.AArch64.Target

/-! Checked literal of a complete address-generation block clear. -/

@[expose] public section

namespace VG

materialize_code Impl.Argon2.AArch64.ClearBlock.code

end VG
