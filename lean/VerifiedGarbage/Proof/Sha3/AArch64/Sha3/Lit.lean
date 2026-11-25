module

public import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sha3.AArch64.Sha3.Vector
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # The literals of the code with FEAT_SHA3 -/

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Sha3.Vector
materialize_code permute
materialize_code absorbBlocks
end VG.Impl.Sha3.AArch64.Sha3.Vector
