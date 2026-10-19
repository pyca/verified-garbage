module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Ntt
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Ntt
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.TCB.AArch64.Target
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.TCB.AArch64.Target

/-!
# ML-DSA on AArch64: the code of the NTTs as literals

The code of `ntt` and `nttInv`, whose tables of zetas are built by functions,
as literals (`materialize_code`, `Proof/Framework/Lit.lean`).
-/

@[expose] public section

namespace VG

materialize_code Impl.MlDsa.AArch64.Arith.ntt
materialize_code Impl.MlDsa.AArch64.Arith.nttInv

end VG
