module

public import VerifiedGarbage.Impl.Argon2.AArch64.Initial
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Argon2.AArch64.Initial
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.AArch64.Target

/-! A checked literal for the six-word H₀ header. -/

@[expose] public section

namespace VG

materialize_code Impl.Argon2.AArch64.Initial.headerCode

end VG
