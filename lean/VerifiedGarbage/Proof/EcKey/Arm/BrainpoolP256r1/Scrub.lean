module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.EcKey.BrainpoolP256r1.ArmFn
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP256r1.Comb
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.BrainpoolP256r1
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.BrainpoolP256r1Decompress
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.CombLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.EcKey.BrainpoolP256r1.ArmFn
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP256r1.Comb
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.BrainpoolP256r1
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.BrainpoolP256r1Decompress
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP256r1.CombLit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# brainpoolP256r1 public keys on 32-bit ARM, without secret residue

`vg_ec_brainpoolp256r1_public_key`, `_compress_public_key` and
`_decompress_public_key`, with and without `umaal`, have no frames: they keep
the registers they save in their scratch buffer, and the field functions they
call do too (`Code.noFrames`, evaluated by `lit_decide` on their literals).
Each is emitted with its cleanup (`Impl.EcKey.Arm.Fn`), and `Fn` below has the
theorem of each, that it meets its contract and returns without secret residue
(`Arm.Scrub.verifiedScrubbed`), which is what its registration binds.
-/

@[expose] public section

namespace VG.Proof.EcKey.Arm.BrainpoolP256r1.Scrub

open VG VG.Arm

theorem publicKey_noFrames : Impl.Ecdsa.Arm.publicKeyBrainpoolP256r1Comb.noFrames = true := by lit_decide

theorem publicKeyU_noFrames : Impl.Ecdsa.Arm.publicKeyBrainpoolP256r1CombU.noFrames = true := by lit_decide

theorem compress_noFrames : Proof.EcKey.Compressed.Arm.BrainpoolP256r1.code.noFrames = true := by lit_decide

theorem compressU_noFrames : Proof.EcKey.Compressed.Arm.BrainpoolP256r1.codeU.noFrames = true := by lit_decide

theorem decompress_noFrames : Proof.EcKey.Compressed.Arm.BrainpoolP256r1Decompress.code.noFrames = true := by lit_decide

theorem decompressU_noFrames : Proof.EcKey.Compressed.Arm.BrainpoolP256r1Decompress.codeU.noFrames = true := by lit_decide

end VG.Proof.EcKey.Arm.BrainpoolP256r1.Scrub

namespace VG.Proof.EcKey.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ec_brainpoolp256r1_public_key`, given the group law. -/
theorem publicKeyBrainpoolP256r1 (hL : Proof.Weierstrass.Law Spec.BrainpoolP256r1.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.publicKeyBrainpoolP256r1
      Proof.EcKey.Arm.BrainpoolP256r1.combPkSpec 32 :=
  verifiedScrubbed (api := Spec.EcKey.BrainpoolP256r1.publicKeyApi)
    { code := Impl.Ecdsa.Arm.publicKeyBrainpoolP256r1Comb
      verified := Proof.EcKey.Arm.BrainpoolP256r1.combPk_verified hL }
    BrainpoolP256r1.Scrub.publicKey_noFrames

/-- `vg_ec_brainpoolp256r1_public_key_umaal`, given the group law. -/
theorem publicKeyBrainpoolP256r1U (hL : Proof.Weierstrass.Law Spec.BrainpoolP256r1.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.publicKeyBrainpoolP256r1U
      Proof.EcKey.Arm.BrainpoolP256r1.combPkSpec 32 :=
  verifiedScrubbed (api := Spec.EcKey.BrainpoolP256r1.publicKeyApi)
    { code := Impl.Ecdsa.Arm.publicKeyBrainpoolP256r1CombU
      verified := Proof.EcKey.Arm.BrainpoolP256r1.combPkU_verified hL }
    BrainpoolP256r1.Scrub.publicKeyU_noFrames

/-- `vg_ec_brainpoolp256r1_compress_public_key`. -/
theorem compressBrainpoolP256r1 :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.compressBrainpoolP256r1
      (Spec.EcKey.BrainpoolP256r1.inst.compressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.BrainpoolP256r1.inst.compressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.BrainpoolP256r1.code
      verified := Proof.EcKey.Compressed.Arm.BrainpoolP256r1.verified }
    BrainpoolP256r1.Scrub.compress_noFrames

/-- `vg_ec_brainpoolp256r1_compress_public_key_umaal`. -/
theorem compressBrainpoolP256r1U :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.compressBrainpoolP256r1U
      (Spec.EcKey.BrainpoolP256r1.inst.compressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.BrainpoolP256r1.inst.compressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.BrainpoolP256r1.codeU
      verified := Proof.EcKey.Compressed.Arm.BrainpoolP256r1.verifiedU }
    BrainpoolP256r1.Scrub.compressU_noFrames

/-- `vg_ec_brainpoolp256r1_decompress_public_key`, given the group law. -/
theorem decompressBrainpoolP256r1 (hL : Proof.Weierstrass.Law Spec.BrainpoolP256r1.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.decompressBrainpoolP256r1
      (Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.BrainpoolP256r1Decompress.code
      verified := Proof.EcKey.Compressed.Arm.BrainpoolP256r1Decompress.verified hL }
    BrainpoolP256r1.Scrub.decompress_noFrames

/-- `vg_ec_brainpoolp256r1_decompress_public_key_umaal`, given the group law. -/
theorem decompressBrainpoolP256r1U (hL : Proof.Weierstrass.Law Spec.BrainpoolP256r1.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.decompressBrainpoolP256r1U
      (Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.BrainpoolP256r1.inst.decompressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.BrainpoolP256r1Decompress.codeU
      verified := Proof.EcKey.Compressed.Arm.BrainpoolP256r1Decompress.verifiedU hL }
    BrainpoolP256r1.Scrub.decompressU_noFrames

end VG.Proof.EcKey.Arm.Fn
