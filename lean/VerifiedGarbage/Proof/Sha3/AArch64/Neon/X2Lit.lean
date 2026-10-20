module

public import VerifiedGarbage.Impl.Sha3.AArch64.Neon.X2
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Sha3.AArch64.Neon.X2
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

@[expose] public section

namespace VG.Impl.Sha3.AArch64.Neon.X2
materialize_code neon := code false
materialize_code sha3 := code true
end VG.Impl.Sha3.AArch64.Neon.X2
