module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Ntt
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Arith.Ntt
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

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
