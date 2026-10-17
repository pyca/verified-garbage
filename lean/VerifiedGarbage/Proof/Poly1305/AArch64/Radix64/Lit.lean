module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.Poly1305.AArch64.Radix64
meta import VerifiedGarbage.Impl.Poly1305.AArch64.Radix64

@[expose] public section

namespace VG
materialize_code Impl.Poly1305.AArch64.Radix64.blocks
materialize_code Impl.Poly1305.AArch64.Radix64.update
materialize_code Impl.Poly1305.AArch64.Radix64.finalize
end VG
