module

public import VerifiedGarbage.Impl.Sha256.AArch64.Stream
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Sha256.AArch64.Stream
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

/-!
# SHA-256 on AArch64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.Sha256.AArch64.compress
materialize_code Impl.Sha256.AArch64.Stream.update
materialize_code Impl.Sha256.AArch64.Stream.finalize

end VG
