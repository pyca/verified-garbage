module

public import VerifiedGarbage.Impl.Sha512.AArch64
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Sha512.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

/-!
# SHA-512 on AArch64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Sha512.AArch64.compress

end VG
