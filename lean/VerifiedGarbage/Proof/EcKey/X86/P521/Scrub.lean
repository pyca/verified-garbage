module

public import VerifiedGarbage.Proof.EcKey.X86.Scrub
public import VerifiedGarbage.Proof.EcKey.X86.P521.Verified
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P521
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P521Decompress
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.EcKey.P521.X86
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P521
import VerifiedGarbage.Proof.EcKey.X86.P521.Lit
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P521
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# P521 public keys on x86 (32-bit), without secret residue

`vg_ec_p521_public_key`, `_compress_public_key` and `_decompress_public_key`,
each, as emitted, followed by the zeroing of the stack its frames and calls use and
`Impl.Scrub.X86.tail` (`X86.Scrub.verifiedScrubbedF`), with their postconditions'
locality from `Proof/EcKey/X86/Scrub.lean`.
-/

@[expose] public section

namespace VG.Proof.EcKey.X86.P521.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.EcKey.X86.Scrub

/-- `vg_ec_p521_public_key`. -/
theorem publicKey_scrubbed (hL : Weierstrass.Law Spec.P521.curve) :
    VerifiedScrubbed target Impl.EcKey.X86.Fn.publicKeyP521 Proof.EcKey.X86.P521.pkSpec 32 :=
  verifiedScrubbedF (api := Spec.EcKey.P521.publicKeyApi)
    { code := Impl.EcKey.X86.publicKeyP521
      verified := Proof.EcKey.X86.P521.pk_verified hL }
    (publicKeyOut Spec.EcKey.P521.inst 20 Impl.Ecdsa.X86.p521Comb.combConsts)

/-- `vg_ec_p521_compress_public_key`. -/
theorem compress_scrubbed :
    VerifiedScrubbed target Impl.EcKey.X86.Fn.compressP521 (Spec.EcKey.P521.inst.compressPublicKeyContract X86.abi 28) 32 :=
  verifiedScrubbedF (api := Spec.EcKey.P521.inst.compressPublicKeyApi)
    { code := Proof.EcKey.Compressed.X86.P521.code
      verified := Proof.EcKey.Compressed.X86.P521.verified }
    (compressOut _ _ [])

/-- `vg_ec_p521_decompress_public_key`. -/
theorem decompress_scrubbed (hL : Weierstrass.Law Spec.P521.curve) :
    VerifiedScrubbed target Impl.EcKey.X86.Fn.decompressP521 (Spec.EcKey.P521.inst.decompressPublicKeyContract X86.abi 28) 32 :=
  verifiedScrubbedF (api := Spec.EcKey.P521.inst.decompressPublicKeyApi)
    { code := Proof.EcKey.Compressed.X86.P521Decompress.code
      verified := Proof.EcKey.Compressed.X86.P521Decompress.verified hL }
    (decompressOut _ _ [])

end VG.Proof.EcKey.X86.P521.Scrub
