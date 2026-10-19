module

public import VerifiedGarbage.Impl.Argon2.AArch64.FillPointers
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Argon2.AArch64.FillPointers
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

/-! Checked literal of the complete filling pointer setup. -/

@[expose] public section

namespace VG

materialize_code Impl.Argon2.AArch64.FillPointers.code

end VG
