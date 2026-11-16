module

public import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Lazy
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sha3.AArch64.Scalar.Lazy
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

@[expose] public section
namespace VG.Impl.Sha3.AArch64.Scalar.Lazy
-- The rounds, which `permute` wraps and `bulk`'s loop contains: evaluated
-- once here, and read by both.
materialize_code permutationCoreCode := (.block permutationCore : Prog VG.AArch64.isa)
materialize_code permute
materialize_code bulk
end VG.Impl.Sha3.AArch64.Scalar.Lazy
