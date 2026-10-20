module

public import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Lit
public import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Lit
public import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitched
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Lit
meta import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Lit
meta import VerifiedGarbage.Impl.ChaCha20Poly1305.AArch64.Stitched
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Tail.Lit
meta import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Tail.Lit

/-!
# ChaCha20-Poly1305 on AArch64: the code as literals
-/

@[expose] public section

namespace VG

materialize_code Impl.ChaCha20Poly1305.AArch64.seal
materialize_code Impl.ChaCha20Poly1305.AArch64.open
materialize_code ChaCha20Poly1305.AArch64.sealScalar :=
  Impl.ChaCha20Poly1305.AArch64.sealMainCode .scalar false
materialize_code ChaCha20Poly1305.AArch64.openScalar :=
  Impl.ChaCha20Poly1305.AArch64.openMainCode .scalar false
materialize_code ChaCha20Poly1305.AArch64.sealNeon :=
  Impl.ChaCha20Poly1305.AArch64.sealMainCode .neon true
materialize_code ChaCha20Poly1305.AArch64.openNeon :=
  Impl.ChaCha20Poly1305.AArch64.openMainCode .neon true
materialize_code ChaCha20Poly1305.AArch64.sealSve2 :=
  Impl.ChaCha20Poly1305.AArch64.sealMainCode .sve2 true
materialize_code ChaCha20Poly1305.AArch64.openSve2 :=
  Impl.ChaCha20Poly1305.AArch64.openMainCode .sve2 true

end VG
