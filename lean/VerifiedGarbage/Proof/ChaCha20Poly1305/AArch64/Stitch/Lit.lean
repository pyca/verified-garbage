module

public import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitch
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitch
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# ChaCha20 and Poly1305 together (AArch64): the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.ChaCha20Poly1305.AArch64.Stitch.bulkSeal
materialize_code Impl.ChaCha20Poly1305.AArch64.Stitch.bulkOpen
materialize_code Impl.ChaCha20Poly1305.AArch64.Stitch.bulkSealSve
materialize_code Impl.ChaCha20Poly1305.AArch64.Stitch.bulkOpenSve

end VG
