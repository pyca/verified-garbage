module

public import VerifiedGarbage.Impl.Ed25519.AArch64.Scalar
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Ed25519.AArch64.Scalar
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.AArch64.Target

/-! The kernel checks this literal once; taint and instruction checks reuse it. -/

@[expose] public section

namespace VG
materialize_code Impl.Ed25519.AArch64.scalarReduce
end VG
