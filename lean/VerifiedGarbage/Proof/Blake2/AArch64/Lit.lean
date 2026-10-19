module

public import VerifiedGarbage.Impl.Blake2.AArch64
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Blake2.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

/-!
# BLAKE2 on AArch64: the code as literals

The code of the compression functions of BLAKE2b and BLAKE2s as literals
(`materialize_code`, `Proof/Framework/Lit.lean`).
-/

@[expose] public section

namespace VG.Proof.Blake2.AArch64

materialize_code compressB := Impl.Blake2.AArch64.compress Spec.Blake2.b
materialize_code compressS := Impl.Blake2.AArch64.compress Spec.Blake2.s

end VG.Proof.Blake2.AArch64
