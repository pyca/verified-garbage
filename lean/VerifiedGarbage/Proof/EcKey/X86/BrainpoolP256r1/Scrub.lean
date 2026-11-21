module

public import VerifiedGarbage.Proof.EcKey.X86.Scrub
public import VerifiedGarbage.Proof.EcKey.X86.BrainpoolP256r1.Verified
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.BrainpoolP256r1
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.BrainpoolP256r1Decompress
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Impl.EcKey.BrainpoolP256r1.X86
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP256r1
import VerifiedGarbage.Proof.EcKey.X86.BrainpoolP256r1.Lit
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP256r1
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# BrainpoolP256r1 public keys on x86 (32-bit), without secret residue

`vg_ec_brainpoolp256r1_public_key`, `_compress_public_key` and `_decompress_public_key`,
each, as emitted, followed by the zeroing of the stack its frames and calls use and
`Impl.Scrub.X86.tail` (`X86.Scrub.verifiedScrubbedAll`), with their postconditions'
locality from `Proof/EcKey/X86/Scrub.lean`.
-/

@[expose] public section

namespace VG.Proof.EcKey.X86.BrainpoolP256r1.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.EcKey.X86.Scrub

/-- `vg_ec_brainpoolp256r1_public_key`. -/
theorem publicKey_scrubbed (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Weierstrass.X86.Inv.InvSounds) :
    VerifiedScrubbed target Impl.EcKey.X86.Fn.publicKeyBrainpoolP256r1 Proof.EcKey.X86.BrainpoolP256r1.pkSpec 32 :=
  verifiedScrubbedAll (api := Spec.EcKey.BrainpoolP256r1.publicKeyApi)
    { code := Impl.EcKey.X86.publicKeyBrainpoolP256r1
      verified := Proof.EcKey.X86.BrainpoolP256r1.pk_verified hL hI }
    (publicKeyOut Spec.EcKey.BrainpoolP256r1.inst 20 Impl.Ecdsa.X86.brainpoolp256r1Comb.combConsts)

/-- `vg_ec_brainpoolp256r1_compress_public_key`. -/
theorem compress_scrubbed (hI : Weierstrass.X86.Inv.InvSounds) :
    VerifiedScrubbed target Impl.EcKey.X86.Fn.compressBrainpoolP256r1 (Spec.EcKey.BrainpoolP256r1.inst.compressPublicKeyContract X86.abi 28) 32 :=
  verifiedScrubbedAll (api := Spec.EcKey.BrainpoolP256r1.inst.compressPublicKeyApi)
    { code := Proof.EcKey.Compressed.X86.BrainpoolP256r1.code
      verified := Proof.EcKey.Compressed.X86.BrainpoolP256r1.verified hI }
    (compressOut _ _ [])

/-- `vg_ec_brainpoolp256r1_decompress_public_key`. -/
theorem decompress_scrubbed (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Weierstrass.X86.Inv.InvSounds) :
    VerifiedScrubbed target Impl.EcKey.X86.Fn.decompressBrainpoolP256r1 (Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyContract X86.abi 28) 32 :=
  verifiedScrubbedAll (api := Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyApi)
    { code := Proof.EcKey.Compressed.X86.BrainpoolP256r1Decompress.code
      verified := Proof.EcKey.Compressed.X86.BrainpoolP256r1Decompress.verified hL hI }
    (decompressOut _ _ [])

end VG.Proof.EcKey.X86.BrainpoolP256r1.Scrub
