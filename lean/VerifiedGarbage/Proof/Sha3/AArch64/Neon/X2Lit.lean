module

public import VerifiedGarbage.Impl.Sha3.AArch64.Neon.X2
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Sha3.AArch64.Neon.X2
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Neon.X2
materialize_code neon := code false
materialize_code sha3 := code true
end VG.Impl.Sha3.AArch64.Neon.X2
