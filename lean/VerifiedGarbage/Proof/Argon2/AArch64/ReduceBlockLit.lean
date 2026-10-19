module

public import VerifiedGarbage.Impl.Argon2.AArch64.ReduceBlock
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Argon2.AArch64.ReduceBlock
import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

@[expose] public section

namespace VG.Impl.Argon2.AArch64.ReduceBlock

materialize_code code

end VG.Impl.Argon2.AArch64.ReduceBlock
