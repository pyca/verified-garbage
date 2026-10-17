module

public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Unrolled
meta import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Unrolled
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Scalar
materialize_code unrolledPermute
end VG.Impl.Sha3.AArch64.Scalar
