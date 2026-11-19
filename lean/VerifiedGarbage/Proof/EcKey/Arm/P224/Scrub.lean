module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.EcKey.Arm.P224.Comb
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P224
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P224Decompress
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.CombLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.EcKey.Arm.P224.Comb
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P224
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P224Decompress
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P224.CombLit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# P-224 public keys on ARMv7, without secret residue

`vg_ec_p224_public_key`, `_compress_public_key` and
`_decompress_public_key`, with and without `umaal`, have no frames: they keep
the registers they save in their scratch buffer, and the field functions they
call do too. Each is registered scrubbed (`Arm.Scrub.scrubReg`): followed by
instructions that set the registers a callee may change, but the result, and
the flags to constants.
-/

@[expose] public section

namespace VG.Proof.EcKey.Arm.P224.Scrub

open VG VG.Arm
open VG.Proof.Weierstrass (Law)

theorem publicKey_noFrames : Impl.Ecdsa.Arm.publicKeyP224Comb.noFrames = true := by lit_decide
theorem publicKeyU_noFrames : Impl.Ecdsa.Arm.publicKeyP224CombU.noFrames = true := by lit_decide
theorem compress_noFrames : Proof.EcKey.Compressed.Arm.P224.code.noFrames = true := by lit_decide
theorem compressU_noFrames : Proof.EcKey.Compressed.Arm.P224.codeU.noFrames = true := by lit_decide
theorem decompress_noFrames : Proof.EcKey.Compressed.Arm.P224Decompress.code.noFrames = true := by lit_decide
theorem decompressU_noFrames : Proof.EcKey.Compressed.Arm.P224Decompress.codeU.noFrames = true := by lit_decide

/-- `Spec.EcKey.P224.publicKeyApi`. -/
def publicKeyReg (hL : Law Spec.P224.curve) : Registration Spec.EcKey.P224.publicKeyApi target :=
  Arm.Scrub.scrubReg {
      code := Impl.Ecdsa.Arm.publicKeyP224Comb
      verified := Proof.EcKey.Arm.P224.combPk_verified hL }
    publicKey_noFrames

/-- `Spec.EcKey.P224.publicKeyApi` with `umaal`. -/
def publicKeyUReg (hL : Law Spec.P224.curve) : Registration Spec.EcKey.P224.publicKeyApi target :=
  Arm.Scrub.scrubReg {
      suffix := "_umaal"
      code := Impl.Ecdsa.Arm.publicKeyP224CombU
      verified := Proof.EcKey.Arm.P224.combPkU_verified hL }
    publicKeyU_noFrames

/-- `Spec.EcKey.P224.inst.compressPublicKeyApi`. -/
def compressReg : Registration Spec.EcKey.P224.inst.compressPublicKeyApi target :=
  Arm.Scrub.scrubReg {
      code := Proof.EcKey.Compressed.Arm.P224.code
      verified := Proof.EcKey.Compressed.Arm.P224.verified }
    compress_noFrames

/-- `Spec.EcKey.P224.inst.compressPublicKeyApi` with `umaal`. -/
def compressUReg : Registration Spec.EcKey.P224.inst.compressPublicKeyApi target :=
  Arm.Scrub.scrubReg {
      suffix := "_umaal"
      code := Proof.EcKey.Compressed.Arm.P224.codeU
      verified := Proof.EcKey.Compressed.Arm.P224.verifiedU }
    compressU_noFrames

/-- `Spec.EcKey.P224.inst.decompressPublicKeyApi`. -/
def decompressReg (hL : Law Spec.P224.curve) : Registration Spec.EcKey.P224.inst.decompressPublicKeyApi target :=
  Arm.Scrub.scrubReg {
      code := Proof.EcKey.Compressed.Arm.P224Decompress.code
      verified := Proof.EcKey.Compressed.Arm.P224Decompress.verified hL }
    decompress_noFrames

/-- `Spec.EcKey.P224.inst.decompressPublicKeyApi` with `umaal`. -/
def decompressUReg (hL : Law Spec.P224.curve) : Registration Spec.EcKey.P224.inst.decompressPublicKeyApi target :=
  Arm.Scrub.scrubReg {
      suffix := "_umaal"
      code := Proof.EcKey.Compressed.Arm.P224Decompress.codeU
      verified := Proof.EcKey.Compressed.Arm.P224Decompress.verifiedU hL }
    decompressU_noFrames

end VG.Proof.EcKey.Arm.P224.Scrub
