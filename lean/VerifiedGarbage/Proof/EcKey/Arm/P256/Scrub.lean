module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.EcKey.P256.ArmFn
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.EcKey.Arm.P256.Comb
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P256
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P256Decompress
import VerifiedGarbage.Proof.Ecdsa.Arm.P256.CombLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.EcKey.P256.ArmFn
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.EcKey.Arm.P256.Comb
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P256
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P256Decompress
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P256.CombLit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# P-256 public keys on 32-bit ARM, without secret residue

`vg_ec_p256_public_key`, `_compress_public_key` and
`_decompress_public_key`, with and without `umaal`, have no frames: they keep
the registers they save in their scratch buffer, and the field functions they
call do too (`Code.noFrames`, evaluated by `lit_decide` on their literals).
Each is emitted with its cleanup (`Impl.EcKey.Arm.Fn`), and `Fn` below has the
theorem of each, that it meets its contract and returns without secret residue
(`Arm.Scrub.verifiedScrubbed`), which is what its registration binds.
-/

@[expose] public section

namespace VG.Proof.EcKey.Arm.P256.Scrub

open VG VG.Arm

theorem publicKey_noFrames : Impl.Ecdsa.Arm.publicKeyP256Comb.noFrames = true := by lit_decide

theorem publicKeyU_noFrames : Impl.Ecdsa.Arm.publicKeyP256CombU.noFrames = true := by lit_decide

theorem compress_noFrames : Proof.EcKey.Compressed.Arm.P256.code.noFrames = true := by lit_decide

theorem compressU_noFrames : Proof.EcKey.Compressed.Arm.P256.codeU.noFrames = true := by lit_decide

theorem decompress_noFrames : Proof.EcKey.Compressed.Arm.P256Decompress.code.noFrames = true := by lit_decide

theorem decompressU_noFrames : Proof.EcKey.Compressed.Arm.P256Decompress.codeU.noFrames = true := by lit_decide

end VG.Proof.EcKey.Arm.P256.Scrub

namespace VG.Proof.EcKey.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ec_p256_public_key`, given the group law. -/
theorem publicKeyP256 (hL : Proof.Weierstrass.Law Spec.P256.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.publicKeyP256
      Proof.EcKey.Arm.P256.combPkSpec 32 :=
  verifiedScrubbed (api := Spec.EcKey.P256.publicKeyApi)
    { code := Impl.Ecdsa.Arm.publicKeyP256Comb
      verified := Proof.EcKey.Arm.P256.combPk_verified hL }
    P256.Scrub.publicKey_noFrames

/-- `vg_ec_p256_public_key_umaal`, given the group law. -/
theorem publicKeyP256U (hL : Proof.Weierstrass.Law Spec.P256.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.publicKeyP256U
      Proof.EcKey.Arm.P256.combPkSpec 32 :=
  verifiedScrubbed (api := Spec.EcKey.P256.publicKeyApi)
    { code := Impl.Ecdsa.Arm.publicKeyP256CombU
      verified := Proof.EcKey.Arm.P256.combPkU_verified hL }
    P256.Scrub.publicKeyU_noFrames

/-- `vg_ec_p256_compress_public_key`. -/
theorem compressP256 :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.compressP256
      (Spec.EcKey.P256.inst.compressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.P256.inst.compressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.P256.code
      verified := Proof.EcKey.Compressed.Arm.P256.verified }
    P256.Scrub.compress_noFrames

/-- `vg_ec_p256_compress_public_key_umaal`. -/
theorem compressP256U :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.compressP256U
      (Spec.EcKey.P256.inst.compressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.P256.inst.compressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.P256.codeU
      verified := Proof.EcKey.Compressed.Arm.P256.verifiedU }
    P256.Scrub.compressU_noFrames

/-- `vg_ec_p256_decompress_public_key`, given the group law. -/
theorem decompressP256 (hL : Proof.Weierstrass.Law Spec.P256.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.decompressP256
      (Spec.EcKey.P256.inst.decompressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.P256.inst.decompressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.P256Decompress.code
      verified := Proof.EcKey.Compressed.Arm.P256Decompress.verified hL }
    P256.Scrub.decompress_noFrames

/-- `vg_ec_p256_decompress_public_key_umaal`, given the group law. -/
theorem decompressP256U (hL : Proof.Weierstrass.Law Spec.P256.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.decompressP256U
      (Spec.EcKey.P256.inst.decompressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.P256.inst.decompressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.P256Decompress.codeU
      verified := Proof.EcKey.Compressed.Arm.P256Decompress.verifiedU hL }
    P256.Scrub.decompressU_noFrames

end VG.Proof.EcKey.Arm.Fn
