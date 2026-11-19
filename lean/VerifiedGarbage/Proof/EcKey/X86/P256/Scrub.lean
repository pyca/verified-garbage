module

public import VerifiedGarbage.Proof.EcKey.X86.Scrub
public import VerifiedGarbage.Proof.EcKey.X86.CombVerified
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P256
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P256Decompress
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P256
import VerifiedGarbage.Proof.EcKey.X86.CombFunction
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P256
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# P256 public keys on x86 (32-bit), without secret residue

`vg_ec_p256_public_key`, `_compress_public_key` and `_decompress_public_key`,
each followed by the zeroing of the stack its frames and calls use and
`Impl.Scrub.X86.tail` (`X86.Scrub.scrubFOf`), with their postconditions'
locality from `Proof/EcKey/X86/Scrub.lean`.
-/

@[expose] public section

namespace VG.Proof.EcKey.X86.P256.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.EcKey.X86.Scrub

/-- `vg_ec_p256_public_key`. -/
def publicKeyReg (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86.Inv.InvSounds) :
    Registration Spec.EcKey.P256.publicKeyApi target :=
  scrubFOf {
      code := Proof.EcKey.X86.pkCombCode
      verified := Proof.EcKey.X86.pkComb_verified hL hI }
    (publicKeyOut Spec.EcKey.P256.inst 20 Impl.Ecdsa.X86.p256Comb.combConsts)

/-- `vg_ec_p256_compress_public_key`. -/
def compressReg (hI : Weierstrass.X86.Inv.InvSounds) :
    Registration Spec.EcKey.P256.inst.compressPublicKeyApi target :=
  scrubFOf {
      code := Proof.EcKey.Compressed.X86.P256.code
      verified := Proof.EcKey.Compressed.X86.P256.verified hI }
    (compressOut _ _ [])

/-- `vg_ec_p256_decompress_public_key`. -/
def decompressReg (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.X86.Inv.InvSounds) :
    Registration Spec.EcKey.P256.inst.decompressPublicKeyApi target :=
  scrubFOf {
      code := Proof.EcKey.Compressed.X86.P256Decompress.code
      verified := Proof.EcKey.Compressed.X86.P256Decompress.verified hL hI }
    (decompressOut _ _ [])

end VG.Proof.EcKey.X86.P256.Scrub
