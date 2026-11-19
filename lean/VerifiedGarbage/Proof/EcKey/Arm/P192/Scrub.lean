module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.EcKey.Arm.P192.Comb
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P192
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P192Decompress
import VerifiedGarbage.Proof.Ecdsa.Arm.P192.CombLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.EcKey.Arm.P192.Comb
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P192
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P192Decompress
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P192.CombLit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# P-192 public keys on ARMv7, without secret residue

`vg_ec_p192_public_key`, `_compress_public_key` and
`_decompress_public_key`, with and without `umaal`, have no frames: they keep
the registers they save in their scratch buffer, and the field functions they
call do too. Each is registered scrubbed (`Arm.Scrub.scrubReg`): followed by
instructions that set the registers a callee may change, but the result, and
the flags to constants.
-/

@[expose] public section

namespace VG.Proof.EcKey.Arm.P192.Scrub

open VG VG.Arm
open VG.Proof.Weierstrass (Law)

theorem publicKey_noFrames : Impl.Ecdsa.Arm.publicKeyP192Comb.noFrames = true := by lit_decide
theorem publicKeyU_noFrames : Impl.Ecdsa.Arm.publicKeyP192CombU.noFrames = true := by lit_decide
theorem compress_noFrames : Proof.EcKey.Compressed.Arm.P192.code.noFrames = true := by lit_decide
theorem compressU_noFrames : Proof.EcKey.Compressed.Arm.P192.codeU.noFrames = true := by lit_decide
theorem decompress_noFrames : Proof.EcKey.Compressed.Arm.P192Decompress.code.noFrames = true := by lit_decide
theorem decompressU_noFrames : Proof.EcKey.Compressed.Arm.P192Decompress.codeU.noFrames = true := by lit_decide

/-- `Spec.EcKey.P192.publicKeyApi`. -/
def publicKeyReg (hL : Law Spec.P192.curve) : Registration Spec.EcKey.P192.publicKeyApi target :=
  Arm.Scrub.scrubReg {
      code := Impl.Ecdsa.Arm.publicKeyP192Comb
      verified := Proof.EcKey.Arm.P192.combPk_verified hL }
    publicKey_noFrames

/-- `Spec.EcKey.P192.publicKeyApi` with `umaal`. -/
def publicKeyUReg (hL : Law Spec.P192.curve) : Registration Spec.EcKey.P192.publicKeyApi target :=
  Arm.Scrub.scrubReg {
      suffix := "_umaal"
      code := Impl.Ecdsa.Arm.publicKeyP192CombU
      verified := Proof.EcKey.Arm.P192.combPkU_verified hL }
    publicKeyU_noFrames

/-- `Spec.EcKey.P192.inst.compressPublicKeyApi`. -/
def compressReg : Registration Spec.EcKey.P192.inst.compressPublicKeyApi target :=
  Arm.Scrub.scrubReg {
      code := Proof.EcKey.Compressed.Arm.P192.code
      verified := Proof.EcKey.Compressed.Arm.P192.verified }
    compress_noFrames

/-- `Spec.EcKey.P192.inst.compressPublicKeyApi` with `umaal`. -/
def compressUReg : Registration Spec.EcKey.P192.inst.compressPublicKeyApi target :=
  Arm.Scrub.scrubReg {
      suffix := "_umaal"
      code := Proof.EcKey.Compressed.Arm.P192.codeU
      verified := Proof.EcKey.Compressed.Arm.P192.verifiedU }
    compressU_noFrames

/-- `Spec.EcKey.P192.inst.decompressPublicKeyApi`. -/
def decompressReg (hL : Law Spec.P192.curve) : Registration Spec.EcKey.P192.inst.decompressPublicKeyApi target :=
  Arm.Scrub.scrubReg {
      code := Proof.EcKey.Compressed.Arm.P192Decompress.code
      verified := Proof.EcKey.Compressed.Arm.P192Decompress.verified hL }
    decompress_noFrames

/-- `Spec.EcKey.P192.inst.decompressPublicKeyApi` with `umaal`. -/
def decompressUReg (hL : Law Spec.P192.curve) : Registration Spec.EcKey.P192.inst.decompressPublicKeyApi target :=
  Arm.Scrub.scrubReg {
      suffix := "_umaal"
      code := Proof.EcKey.Compressed.Arm.P192Decompress.codeU
      verified := Proof.EcKey.Compressed.Arm.P192Decompress.verifiedU hL }
    decompressU_noFrames

end VG.Proof.EcKey.Arm.P192.Scrub
