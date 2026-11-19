module

public import VerifiedGarbage.Proof.EcKey.X86.Scrub
public import VerifiedGarbage.Proof.EcKey.X86.P384.Verified
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P384
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.P384Decompress
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.P384
import VerifiedGarbage.Proof.EcKey.X86.P384.Lit
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.P384
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# P384 public keys on x86 (32-bit), without secret residue

`vg_ec_p384_public_key`, `_compress_public_key` and `_decompress_public_key`,
each followed by the zeroing of the stack its frames and calls use and
`Impl.Scrub.X86.tail` (`X86.Scrub.scrubFOf`), with their postconditions'
locality from `Proof/EcKey/X86/Scrub.lean`.
-/

@[expose] public section

namespace VG.Proof.EcKey.X86.P384.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.EcKey.X86.Scrub

/-- `vg_ec_p384_public_key`. -/
def publicKeyReg (hL : Weierstrass.Law Spec.P384.curve) :
    Registration Spec.EcKey.P384.publicKeyApi target :=
  scrubFOf {
      code := Impl.EcKey.X86.publicKeyP384
      verified := Proof.EcKey.X86.P384.pk_verified hL }
    (publicKeyOut Spec.EcKey.P384.inst 20 Impl.Ecdsa.X86.p384Comb.combConsts)

/-- `vg_ec_p384_compress_public_key`. -/
def compressReg :
    Registration Spec.EcKey.P384.inst.compressPublicKeyApi target :=
  scrubFOf {
      code := Proof.EcKey.Compressed.X86.P384.code
      verified := Proof.EcKey.Compressed.X86.P384.verified }
    (compressOut _ _ [])

/-- `vg_ec_p384_decompress_public_key`. -/
def decompressReg (hL : Weierstrass.Law Spec.P384.curve) :
    Registration Spec.EcKey.P384.inst.decompressPublicKeyApi target :=
  scrubFOf {
      code := Proof.EcKey.Compressed.X86.P384Decompress.code
      verified := Proof.EcKey.Compressed.X86.P384Decompress.verified hL }
    (decompressOut _ _ [])

end VG.Proof.EcKey.X86.P384.Scrub
