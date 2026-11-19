module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP384r1.Comb
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.BrainpoolP384r1
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.BrainpoolP384r1Decompress
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP384r1.CombLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP384r1.Comb
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.BrainpoolP384r1
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.BrainpoolP384r1Decompress
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP384r1.CombLit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# brainpoolP384r1 public keys on ARMv7, without secret residue

`vg_ec_brainpoolp384r1_public_key`, `_compress_public_key` and
`_decompress_public_key`, with and without `umaal`, have no frames: they keep
the registers they save in their scratch buffer, and the field functions they
call do too. Each is registered scrubbed (`Arm.Scrub.scrubReg`): followed by
instructions that set the registers a callee may change, but the result, and
the flags to constants.
-/

@[expose] public section

namespace VG.Proof.EcKey.Arm.BrainpoolP384r1.Scrub

open VG VG.Arm
open VG.Proof.Weierstrass (Law)

theorem publicKey_noFrames : Impl.Ecdsa.Arm.publicKeyBrainpoolP384r1Comb.noFrames = true := by lit_decide
theorem publicKeyU_noFrames : Impl.Ecdsa.Arm.publicKeyBrainpoolP384r1CombU.noFrames = true := by lit_decide
theorem compress_noFrames : Proof.EcKey.Compressed.Arm.BrainpoolP384r1.code.noFrames = true := by lit_decide
theorem compressU_noFrames : Proof.EcKey.Compressed.Arm.BrainpoolP384r1.codeU.noFrames = true := by lit_decide
theorem decompress_noFrames : Proof.EcKey.Compressed.Arm.BrainpoolP384r1Decompress.code.noFrames = true := by lit_decide
theorem decompressU_noFrames : Proof.EcKey.Compressed.Arm.BrainpoolP384r1Decompress.codeU.noFrames = true := by lit_decide

/-- `Spec.EcKey.BrainpoolP384r1.publicKeyApi`. -/
def publicKeyReg (hL : Law Spec.BrainpoolP384r1.curve) : Registration Spec.EcKey.BrainpoolP384r1.publicKeyApi target :=
  Arm.Scrub.scrubReg {
      code := Impl.Ecdsa.Arm.publicKeyBrainpoolP384r1Comb
      verified := Proof.EcKey.Arm.BrainpoolP384r1.combPk_verified hL }
    publicKey_noFrames

/-- `Spec.EcKey.BrainpoolP384r1.publicKeyApi` with `umaal`. -/
def publicKeyUReg (hL : Law Spec.BrainpoolP384r1.curve) : Registration Spec.EcKey.BrainpoolP384r1.publicKeyApi target :=
  Arm.Scrub.scrubReg {
      suffix := "_umaal"
      code := Impl.Ecdsa.Arm.publicKeyBrainpoolP384r1CombU
      verified := Proof.EcKey.Arm.BrainpoolP384r1.combPkU_verified hL }
    publicKeyU_noFrames

/-- `Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyApi`. -/
def compressReg : Registration Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyApi target :=
  Arm.Scrub.scrubReg {
      code := Proof.EcKey.Compressed.Arm.BrainpoolP384r1.code
      verified := Proof.EcKey.Compressed.Arm.BrainpoolP384r1.verified }
    compress_noFrames

/-- `Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyApi` with `umaal`. -/
def compressUReg : Registration Spec.EcKey.BrainpoolP384r1.inst.compressPublicKeyApi target :=
  Arm.Scrub.scrubReg {
      suffix := "_umaal"
      code := Proof.EcKey.Compressed.Arm.BrainpoolP384r1.codeU
      verified := Proof.EcKey.Compressed.Arm.BrainpoolP384r1.verifiedU }
    compressU_noFrames

/-- `Spec.EcKey.BrainpoolP384r1.inst.decompressPublicKeyApi`. -/
def decompressReg (hL : Law Spec.BrainpoolP384r1.curve) : Registration Spec.EcKey.BrainpoolP384r1.inst.decompressPublicKeyApi target :=
  Arm.Scrub.scrubReg {
      code := Proof.EcKey.Compressed.Arm.BrainpoolP384r1Decompress.code
      verified := Proof.EcKey.Compressed.Arm.BrainpoolP384r1Decompress.verified hL }
    decompress_noFrames

/-- `Spec.EcKey.BrainpoolP384r1.inst.decompressPublicKeyApi` with `umaal`. -/
def decompressUReg (hL : Law Spec.BrainpoolP384r1.curve) : Registration Spec.EcKey.BrainpoolP384r1.inst.decompressPublicKeyApi target :=
  Arm.Scrub.scrubReg {
      suffix := "_umaal"
      code := Proof.EcKey.Compressed.Arm.BrainpoolP384r1Decompress.codeU
      verified := Proof.EcKey.Compressed.Arm.BrainpoolP384r1Decompress.verifiedU hL }
    decompressU_noFrames

end VG.Proof.EcKey.Arm.BrainpoolP384r1.Scrub
