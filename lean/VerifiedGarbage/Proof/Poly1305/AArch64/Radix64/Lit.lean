module

public import VerifiedGarbage.Impl.Poly1305.AArch64.Radix64
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Poly1305.AArch64.Radix64
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit

@[expose] public section

namespace VG
materialize_code Impl.Poly1305.AArch64.Radix64.blocks
materialize_code Impl.Poly1305.AArch64.Radix64.update
materialize_code Impl.Poly1305.AArch64.Radix64.finalize
end VG
