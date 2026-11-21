module

public import VerifiedGarbage.Proof.EcKey.X86.Scrub
public import VerifiedGarbage.Proof.EcKey.X86.BrainpoolP512r1.Verified
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.BrainpoolP512r1
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.BrainpoolP512r1Decompress
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Impl.EcKey.BrainpoolP512r1.X86
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP512r1
import VerifiedGarbage.Proof.EcKey.X86.BrainpoolP512r1.Lit
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP512r1
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# BrainpoolP512r1 public keys on x86 (32-bit), without secret residue

`vg_ec_brainpoolp512r1_public_key`, `_compress_public_key` and `_decompress_public_key`,
each, as emitted, followed by the zeroing of the stack its frames and calls use and
`Impl.Scrub.X86.tail` (`X86.Scrub.verifiedScrubbedAll`), with their postconditions'
locality from `Proof/EcKey/X86/Scrub.lean`.
-/

@[expose] public section

namespace VG.Proof.EcKey.X86.BrainpoolP512r1.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.EcKey.X86.Scrub

/-- `vg_ec_brainpoolp512r1_public_key`. -/
theorem publicKey_scrubbed (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    VerifiedScrubbed target Impl.EcKey.X86.Fn.publicKeyBrainpoolP512r1 Proof.EcKey.X86.BrainpoolP512r1.pkSpec 32 :=
  verifiedScrubbedAll (api := Spec.EcKey.BrainpoolP512r1.publicKeyApi)
    { code := Impl.EcKey.X86.publicKeyBrainpoolP512r1
      verified := Proof.EcKey.X86.BrainpoolP512r1.pk_verified hL }
    (publicKeyOut Spec.EcKey.BrainpoolP512r1.inst 20 Impl.Ecdsa.X86.brainpoolp512r1Comb.combConsts)

/-- `vg_ec_brainpoolp512r1_compress_public_key`. -/
theorem compress_scrubbed :
    VerifiedScrubbed target Impl.EcKey.X86.Fn.compressBrainpoolP512r1 (Spec.EcKey.BrainpoolP512r1.inst.compressPublicKeyContract X86.abi 28) 32 :=
  verifiedScrubbedAll (api := Spec.EcKey.BrainpoolP512r1.inst.compressPublicKeyApi)
    { code := Proof.EcKey.Compressed.X86.BrainpoolP512r1.code
      verified := Proof.EcKey.Compressed.X86.BrainpoolP512r1.verified }
    (compressOut _ _ [])

/-- `vg_ec_brainpoolp512r1_decompress_public_key`. -/
theorem decompress_scrubbed (hL : Weierstrass.Law Spec.BrainpoolP512r1.curve) :
    VerifiedScrubbed target Impl.EcKey.X86.Fn.decompressBrainpoolP512r1 (Spec.EcKey.BrainpoolP512r1.inst.decompressPublicKeyContract X86.abi 28) 32 :=
  verifiedScrubbedAll (api := Spec.EcKey.BrainpoolP512r1.inst.decompressPublicKeyApi)
    { code := Proof.EcKey.Compressed.X86.BrainpoolP512r1Decompress.code
      verified := Proof.EcKey.Compressed.X86.BrainpoolP512r1Decompress.verified hL }
    (decompressOut _ _ [])

end VG.Proof.EcKey.X86.BrainpoolP512r1.Scrub
