module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.Poly1305.AArch64.Vector
meta import VerifiedGarbage.Impl.Poly1305.AArch64.Vector

@[expose] public section

namespace VG
materialize_code Impl.Poly1305.AArch64.Vector.update
end VG
