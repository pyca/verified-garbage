module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitched
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitched

/-!
# ChaCha20-Poly1305 on AArch64, the rest when encrypting: the code as a literal
-/

@[expose] public section

namespace VG

materialize_code Impl.ChaCha20Poly1305.AArch64.Tail.rest

end VG
