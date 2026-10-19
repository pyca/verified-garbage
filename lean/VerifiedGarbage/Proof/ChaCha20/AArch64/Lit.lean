module

public import VerifiedGarbage.Impl.ChaCha20.AArch64.Xor
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.ChaCha20.AArch64.Xor
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

/-!
# ChaCha20 on AArch64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.ChaCha20.AArch64.block
materialize_code Impl.ChaCha20.AArch64.Xor.xor

end VG
