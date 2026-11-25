module

public import VerifiedGarbage.Impl.Sha3.AArch64.Hybrid.X3
public import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sha3.AArch64.Hybrid.X3
meta import VerifiedGarbage.Proof.Sha3.AArch64.Scalar.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-! # The literals of the code on three states -/

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Hybrid.X3
materialize_code scalar
materialize_code vector
materialize_code baseline := code false
materialize_code sha3 := code true
end VG.Impl.Sha3.AArch64.Hybrid.X3
