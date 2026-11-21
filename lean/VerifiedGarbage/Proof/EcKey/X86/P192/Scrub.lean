module

public import VerifiedGarbage.Proof.EcKey.X86.Scrub
public import VerifiedGarbage.Proof.EcKey.X86.P192.Verified
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P192
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P192Decompress
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Impl.EcKey.P192.X86
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P192
import VerifiedGarbage.Proof.EcKey.X86.P192.Lit
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P192
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# P192 public keys on x86 (32-bit), without secret residue

`vg_ec_p192_public_key`, `_compress_public_key` and `_decompress_public_key`,
each, as emitted, followed by the zeroing of the stack its frames and calls use and
`Impl.Scrub.X86.tail` (`X86.Scrub.verifiedScrubbedAll`), with their postconditions'
locality from `Proof/EcKey/X86/Scrub.lean`.
-/

@[expose] public section

namespace VG.Proof.EcKey.X86.P192.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.EcKey.X86.Scrub

/-- `vg_ec_p192_public_key`. -/
theorem publicKey_scrubbed (hL : Weierstrass.Law Spec.P192.curve) :
    VerifiedScrubbed target Impl.EcKey.X86.Fn.publicKeyP192 Proof.EcKey.X86.P192.pkSpec 32 :=
  verifiedScrubbedAll (api := Spec.EcKey.P192.publicKeyApi)
    { code := Impl.EcKey.X86.publicKeyP192
      verified := Proof.EcKey.X86.P192.pk_verified hL }
    (publicKeyOut Spec.EcKey.P192.inst 20 Impl.Ecdsa.X86.p192Comb.combConsts)

/-- `vg_ec_p192_compress_public_key`. -/
theorem compress_scrubbed :
    VerifiedScrubbed target Impl.EcKey.X86.Fn.compressP192 (Spec.EcKey.P192.inst.compressPublicKeyContract X86.abi 28) 32 :=
  verifiedScrubbedAll (api := Spec.EcKey.P192.inst.compressPublicKeyApi)
    { code := Proof.EcKey.Compressed.X86.P192.code
      verified := Proof.EcKey.Compressed.X86.P192.verified }
    (compressOut _ _ [])

/-- `vg_ec_p192_decompress_public_key`. -/
theorem decompress_scrubbed (hL : Weierstrass.Law Spec.P192.curve) :
    VerifiedScrubbed target Impl.EcKey.X86.Fn.decompressP192 (Spec.EcKey.P192.inst.decompressPublicKeyContract X86.abi 28) 32 :=
  verifiedScrubbedAll (api := Spec.EcKey.P192.inst.decompressPublicKeyApi)
    { code := Proof.EcKey.Compressed.X86.P192Decompress.code
      verified := Proof.EcKey.Compressed.X86.P192Decompress.verified hL }
    (decompressOut _ _ [])

end VG.Proof.EcKey.X86.P192.Scrub
