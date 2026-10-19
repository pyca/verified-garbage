module

public import VerifiedGarbage.Impl.Rc4.AArch64
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Rc4.AArch64
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

/-! Literal code keeps the unrolled groups cheap for kernel-evaluated audits. -/

@[expose] public section

namespace VG.Impl.Rc4.AArch64
materialize_code applyRest
materialize_code apply
materialize_code init
end VG.Impl.Rc4.AArch64
