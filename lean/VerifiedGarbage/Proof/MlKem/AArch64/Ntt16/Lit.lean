module

public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.AArch64.Target

/-! # Literals of the 16-bit NTT and its inverse, for the checks the kernel evaluates -/

@[expose] public section

namespace VG.Impl.MlKem.AArch64.Ntt16

materialize_code ntt
materialize_code nttInv

end VG.Impl.MlKem.AArch64.Ntt16
