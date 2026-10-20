module

public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Resident
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.UnrolledLit
meta import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Resident
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.UnrolledLit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Scalar.Resident
materialize_code bulk
end VG.Impl.Sha3.AArch64.Scalar.Resident
