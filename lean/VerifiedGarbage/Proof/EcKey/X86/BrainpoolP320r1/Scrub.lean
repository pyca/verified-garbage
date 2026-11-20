module

public import VerifiedGarbage.Proof.EcKey.X86.Scrub
public import VerifiedGarbage.Proof.EcKey.X86.BrainpoolP320r1.Verified
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.BrainpoolP320r1
public import VerifiedGarbage.Proof.EcKey.Compressed.X86.BrainpoolP320r1Decompress
public import VerifiedGarbage.Proof.Framework.X86.ScrubProved
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Spec.EcKey.BrainpoolP320r1
import VerifiedGarbage.Proof.EcKey.X86.BrainpoolP320r1.Lit
import VerifiedGarbage.Proof.Weierstrass.X86.MontLit.BrainpoolP320r1
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.Lit

/-!
# BrainpoolP320r1 public keys on x86 (32-bit), without secret residue

`vg_ec_brainpoolp320r1_public_key`, `_compress_public_key` and `_decompress_public_key`,
each followed by the zeroing of the stack its frames and calls use and
`Impl.Scrub.X86.tail` (`X86.Scrub.scrubFOf`), with their postconditions'
locality from `Proof/EcKey/X86/Scrub.lean`.
-/

@[expose] public section

namespace VG.Proof.EcKey.X86.BrainpoolP320r1.Scrub

open VG.X86 VG.X86.Scrub VG.Proof.EcKey.X86.Scrub

/-- `vg_ec_brainpoolp320r1_public_key`. -/
def publicKeyReg (hL : Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    Registration Spec.EcKey.BrainpoolP320r1.publicKeyApi target :=
  scrubFOf {
      code := Impl.EcKey.X86.publicKeyBrainpoolP320r1
      verified := Proof.EcKey.X86.BrainpoolP320r1.pk_verified hL }
    (publicKeyOut Spec.EcKey.BrainpoolP320r1.inst 20 Impl.Ecdsa.X86.brainpoolp320r1Comb.combConsts)

/-- `vg_ec_brainpoolp320r1_compress_public_key`. -/
def compressReg :
    Registration Spec.EcKey.BrainpoolP320r1.inst.compressPublicKeyApi target :=
  scrubFOf {
      code := Proof.EcKey.Compressed.X86.BrainpoolP320r1.code
      verified := Proof.EcKey.Compressed.X86.BrainpoolP320r1.verified }
    (compressOut _ _ [])

/-- `vg_ec_brainpoolp320r1_decompress_public_key`. -/
def decompressReg (hL : Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    Registration Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyApi target :=
  scrubFOf {
      code := Proof.EcKey.Compressed.X86.BrainpoolP320r1Decompress.code
      verified := Proof.EcKey.Compressed.X86.BrainpoolP320r1Decompress.verified hL }
    (decompressOut _ _ [])

end VG.Proof.EcKey.X86.BrainpoolP320r1.Scrub
