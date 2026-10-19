module

public import VerifiedGarbage.Impl.Scrypt.AArch64.RoMix
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Scrypt.AArch64.RoMix
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

/-!
# scrypt on AArch64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Scrypt.AArch64.salsa
materialize_code Impl.Scrypt.AArch64.blockMix
materialize_code Impl.Scrypt.AArch64.roMix

end VG
