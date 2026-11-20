module

public import VerifiedGarbage.Proof.EcKey.X86.Scrub
public import VerifiedGarbage.Proof.EcKey.X86.P224.Verified
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P224
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P224Decompress
public import VerifiedGarbage.Proof.Framework.X86.ScrubFn
public import VerifiedGarbage.Impl.EcKey.P224.X86
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P224
import VerifiedGarbage.Proof.EcKey.X86.P224.Lit
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P224
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# P224 public keys on x86 (32-bit), without secret residue

`vg_ec_p224_public_key`, `_compress_public_key` and `_decompress_public_key`,
each, as emitted, followed by the zeroing of the stack its frames and calls use and
`Impl.Scrub.X86.tail` (`X86.Scrub.verifiedScrubbedF`), with their postconditions'
locality from `Proof/EcKey/X86/Scrub.lean`.
-/

@[expose] public section

namespace VG.Proof.EcKey.X86.P224.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.EcKey.X86.Scrub

/-- `vg_ec_p224_public_key`. -/
theorem publicKey_scrubbed (hL : Weierstrass.Law Spec.P224.curve) :
    VerifiedScrubbed target Impl.EcKey.X86.Fn.publicKeyP224 Proof.EcKey.X86.P224.pkSpec 32 :=
  verifiedScrubbedF (api := Spec.EcKey.P224.publicKeyApi)
    { code := Impl.EcKey.X86.publicKeyP224
      verified := Proof.EcKey.X86.P224.pk_verified hL }
    (publicKeyOut Spec.EcKey.P224.inst 20 Impl.Ecdsa.X86.p224Comb.combConsts)

/-- `vg_ec_p224_compress_public_key`. -/
theorem compress_scrubbed :
    VerifiedScrubbed target Impl.EcKey.X86.Fn.compressP224 (Spec.EcKey.P224.inst.compressPublicKeyContract X86.abi 28) 32 :=
  verifiedScrubbedF (api := Spec.EcKey.P224.inst.compressPublicKeyApi)
    { code := Proof.EcKey.Compressed.X86.P224.code
      verified := Proof.EcKey.Compressed.X86.P224.verified }
    (compressOut _ _ [])

/-- `vg_ec_p224_decompress_public_key`. -/
theorem decompress_scrubbed (hL : Weierstrass.Law Spec.P224.curve) :
    VerifiedScrubbed target Impl.EcKey.X86.Fn.decompressP224 (Spec.EcKey.P224.inst.decompressPublicKeyContract X86.abi 28) 32 :=
  verifiedScrubbedF (api := Spec.EcKey.P224.inst.decompressPublicKeyApi)
    { code := Proof.EcKey.Compressed.X86.P224Decompress.code
      verified := Proof.EcKey.Compressed.X86.P224Decompress.verified hL }
    (decompressOut _ _ [])

end VG.Proof.EcKey.X86.P224.Scrub
