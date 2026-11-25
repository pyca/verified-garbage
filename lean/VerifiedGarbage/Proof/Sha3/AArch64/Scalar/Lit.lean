module

public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Core
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Core
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # The literals of the code in general registers -/

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Scalar
materialize_code core
materialize_code permute
materialize_code absorbBlocks
end VG.Impl.Sha3.AArch64.Scalar
