module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP320r1.Comb
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.BrainpoolP320r1
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.BrainpoolP320r1Decompress
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP320r1.CombLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP320r1.Comb
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.BrainpoolP320r1
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.BrainpoolP320r1Decompress
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP320r1.CombLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# brainpoolP320r1 public keys on 32-bit ARM, without secret residue

`vg_ec_brainpoolp320r1_public_key`, `_compress_public_key` and
`_decompress_public_key`, with either multiplication of the field, have no
frames: they keep the registers they save in their scratch space, a buffer.
Each is registered scrubbed (`Arm.Scrub.scrubReg`): followed by instructions
that set the registers a callee may change, but the result, and the flags to
constants.
-/

@[expose] public section

namespace VG.Proof.EcKey.Arm.BrainpoolP320r1.Scrub

open VG VG.Arm

theorem publicKey_noFrames : Impl.Ecdsa.Arm.publicKeyBrainpoolP320r1Comb.noFrames = true := by lit_decide

theorem publicKeyU_noFrames : Impl.Ecdsa.Arm.publicKeyBrainpoolP320r1CombU.noFrames = true := by lit_decide

theorem compress_noFrames : Compressed.Arm.BrainpoolP320r1.code.noFrames = true := by lit_decide

theorem compressU_noFrames : Compressed.Arm.BrainpoolP320r1.codeU.noFrames = true := by lit_decide

theorem decompress_noFrames : Compressed.Arm.BrainpoolP320r1Decompress.code.noFrames = true := by lit_decide

theorem decompressU_noFrames : Compressed.Arm.BrainpoolP320r1Decompress.codeU.noFrames = true := by lit_decide

/-- `vg_ec_brainpoolp320r1_public_key`, given the group law. -/
def publicKeyReg (hC : Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    Registration Spec.EcKey.BrainpoolP320r1.publicKeyApi target :=
  Arm.Scrub.scrubReg {
      code := Impl.Ecdsa.Arm.publicKeyBrainpoolP320r1Comb
      verified := combPk_verified hC }
    publicKey_noFrames

/-- `vg_ec_brainpoolp320r1_public_key_umaal`, given the group law. -/
def publicKeyUReg (hC : Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    Registration Spec.EcKey.BrainpoolP320r1.publicKeyApi target :=
  Arm.Scrub.scrubReg {
      suffix := "_umaal"
      code := Impl.Ecdsa.Arm.publicKeyBrainpoolP320r1CombU
      verified := combPkU_verified hC }
    publicKeyU_noFrames

/-- `vg_ec_brainpoolp320r1_compress_public_key`. -/
def compressReg : Registration Spec.EcKey.BrainpoolP320r1.inst.compressPublicKeyApi target :=
  Arm.Scrub.scrubReg {
      code := Compressed.Arm.BrainpoolP320r1.code
      verified := Compressed.Arm.BrainpoolP320r1.verified }
    compress_noFrames

/-- `vg_ec_brainpoolp320r1_compress_public_key_umaal`. -/
def compressUReg : Registration Spec.EcKey.BrainpoolP320r1.inst.compressPublicKeyApi target :=
  Arm.Scrub.scrubReg {
      suffix := "_umaal"
      code := Compressed.Arm.BrainpoolP320r1.codeU
      verified := Compressed.Arm.BrainpoolP320r1.verifiedU }
    compressU_noFrames

/-- `vg_ec_brainpoolp320r1_decompress_public_key`, given the group law. -/
def decompressReg (hC : Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    Registration Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyApi target :=
  Arm.Scrub.scrubReg {
      code := Compressed.Arm.BrainpoolP320r1Decompress.code
      verified := Compressed.Arm.BrainpoolP320r1Decompress.verified hC }
    decompress_noFrames

/-- `vg_ec_brainpoolp320r1_decompress_public_key_umaal`, given the group law. -/
def decompressUReg (hC : Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    Registration Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyApi target :=
  Arm.Scrub.scrubReg {
      suffix := "_umaal"
      code := Compressed.Arm.BrainpoolP320r1Decompress.codeU
      verified := Compressed.Arm.BrainpoolP320r1Decompress.verifiedU hC }
    decompressU_noFrames

end VG.Proof.EcKey.Arm.BrainpoolP320r1.Scrub
