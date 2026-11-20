module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.EcKey.Secp256k1.ArmFn
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.EcKey.Arm.Secp256k1.CombVerified
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Secp256k1
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Secp256k1Decompress
import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.EcKey.Secp256k1.ArmFn
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.EcKey.Arm.Secp256k1.CombVerified
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Secp256k1
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.Secp256k1Decompress
meta import VerifiedGarbage.Proof.Ecdsa.Arm.Secp256k1.CombLit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# secp256k1 public keys on 32-bit ARM, without secret residue

`vg_ec_secp256k1_public_key`, `_compress_public_key` and
`_decompress_public_key`, with and without `umaal`, have no frames: they keep
the registers they save in their scratch buffer, and the field functions they
call do too (`Code.noFrames`, evaluated by `lit_decide` on their literals).
Each is emitted with its cleanup (`Impl.EcKey.Arm.Fn`), and `Fn` below has the
theorem of each, that it meets its contract and returns without secret residue
(`Arm.Scrub.verifiedScrubbed`), which is what its registration binds.
-/

@[expose] public section

namespace VG.Proof.EcKey.Arm.Secp256k1.Scrub

open VG VG.Arm

theorem publicKey_noFrames : Impl.Ecdsa.Arm.publicKeySecp256k1Comb.noFrames = true := by lit_decide

theorem publicKeyU_noFrames : Impl.Ecdsa.Arm.publicKeySecp256k1CombU.noFrames = true := by lit_decide

theorem compress_noFrames : Proof.EcKey.Compressed.Arm.Secp256k1.code.noFrames = true := by lit_decide

theorem compressU_noFrames : Proof.EcKey.Compressed.Arm.Secp256k1.codeU.noFrames = true := by lit_decide

theorem decompress_noFrames : Proof.EcKey.Compressed.Arm.Secp256k1Decompress.code.noFrames = true := by lit_decide

theorem decompressU_noFrames : Proof.EcKey.Compressed.Arm.Secp256k1Decompress.codeU.noFrames = true := by lit_decide

end VG.Proof.EcKey.Arm.Secp256k1.Scrub

namespace VG.Proof.EcKey.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ec_secp256k1_public_key`, given the group law. -/
theorem publicKeySecp256k1 (hL : Proof.Weierstrass.Law Spec.Secp256k1.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.publicKeySecp256k1
      Proof.EcKey.Arm.Secp256k1.combPkSpec 32 :=
  verifiedScrubbed (api := Spec.EcKey.Secp256k1.publicKeyApi)
    { code := Impl.Ecdsa.Arm.publicKeySecp256k1Comb
      verified := Proof.EcKey.Arm.Secp256k1.combPk_verified hL }
    Secp256k1.Scrub.publicKey_noFrames

/-- `vg_ec_secp256k1_public_key_umaal`, given the group law. -/
theorem publicKeySecp256k1U (hL : Proof.Weierstrass.Law Spec.Secp256k1.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.publicKeySecp256k1U
      Proof.EcKey.Arm.Secp256k1.combPkSpec 32 :=
  verifiedScrubbed (api := Spec.EcKey.Secp256k1.publicKeyApi)
    { code := Impl.Ecdsa.Arm.publicKeySecp256k1CombU
      verified := Proof.EcKey.Arm.Secp256k1.combPkU_verified hL }
    Secp256k1.Scrub.publicKeyU_noFrames

/-- `vg_ec_secp256k1_compress_public_key`. -/
theorem compressSecp256k1 :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.compressSecp256k1
      (Spec.EcKey.Secp256k1.inst.compressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.Secp256k1.inst.compressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.Secp256k1.code
      verified := Proof.EcKey.Compressed.Arm.Secp256k1.verified }
    Secp256k1.Scrub.compress_noFrames

/-- `vg_ec_secp256k1_compress_public_key_umaal`. -/
theorem compressSecp256k1U :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.compressSecp256k1U
      (Spec.EcKey.Secp256k1.inst.compressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.Secp256k1.inst.compressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.Secp256k1.codeU
      verified := Proof.EcKey.Compressed.Arm.Secp256k1.verifiedU }
    Secp256k1.Scrub.compressU_noFrames

/-- `vg_ec_secp256k1_decompress_public_key`, given the group law. -/
theorem decompressSecp256k1 (hL : Proof.Weierstrass.Law Spec.Secp256k1.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.decompressSecp256k1
      (Spec.EcKey.Secp256k1.inst.decompressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.Secp256k1Decompress.code
      verified := Proof.EcKey.Compressed.Arm.Secp256k1Decompress.verified hL }
    Secp256k1.Scrub.decompress_noFrames

/-- `vg_ec_secp256k1_decompress_public_key_umaal`, given the group law. -/
theorem decompressSecp256k1U (hL : Proof.Weierstrass.Law Spec.Secp256k1.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.decompressSecp256k1U
      (Spec.EcKey.Secp256k1.inst.decompressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.Secp256k1.inst.decompressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.Secp256k1Decompress.codeU
      verified := Proof.EcKey.Compressed.Arm.Secp256k1Decompress.verifiedU hL }
    Secp256k1.Scrub.decompressU_noFrames

end VG.Proof.EcKey.Arm.Fn
