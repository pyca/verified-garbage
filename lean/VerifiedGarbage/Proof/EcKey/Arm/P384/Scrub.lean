module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.EcKey.P384.ArmFn
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.EcKey.Arm.P384.Comb
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P384
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P384Decompress
import VerifiedGarbage.Proof.Ecdsa.Arm.P384.CombLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.EcKey.P384.ArmFn
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.EcKey.Arm.P384.Comb
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P384
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P384Decompress
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P384.CombLit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# P-384 public keys on 32-bit ARM, without secret residue

`vg_ec_p384_public_key`, `_compress_public_key` and
`_decompress_public_key`, with and without `umaal`, have no frames: they keep
the registers they save in their scratch buffer, and the field functions they
call do too (`Code.noFrames`, evaluated by `lit_decide` on their literals).
Each is emitted with its cleanup (`Impl.EcKey.Arm.Fn`), and `Fn` below has the
theorem of each, that it meets its contract and returns without secret residue
(`Arm.Scrub.verifiedScrubbed`), which is what its registration binds.
-/

@[expose] public section

namespace VG.Proof.EcKey.Arm.P384.Scrub

open VG VG.Arm

theorem publicKey_noFrames : Impl.Ecdsa.Arm.publicKeyP384Comb.noFrames = true := by lit_decide

theorem publicKeyU_noFrames : Impl.Ecdsa.Arm.publicKeyP384CombU.noFrames = true := by lit_decide

theorem compress_noFrames : Proof.EcKey.Compressed.Arm.P384.code.noFrames = true := by lit_decide

theorem compressU_noFrames : Proof.EcKey.Compressed.Arm.P384.codeU.noFrames = true := by lit_decide

theorem decompress_noFrames : Proof.EcKey.Compressed.Arm.P384Decompress.code.noFrames = true := by lit_decide

theorem decompressU_noFrames : Proof.EcKey.Compressed.Arm.P384Decompress.codeU.noFrames = true := by lit_decide

end VG.Proof.EcKey.Arm.P384.Scrub

namespace VG.Proof.EcKey.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ec_p384_public_key`, given the group law. -/
theorem publicKeyP384 (hL : Proof.Weierstrass.Law Spec.P384.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.publicKeyP384
      Proof.EcKey.Arm.P384.combPkSpec 32 :=
  verifiedScrubbed (api := Spec.EcKey.P384.publicKeyApi)
    { code := Impl.Ecdsa.Arm.publicKeyP384Comb
      verified := Proof.EcKey.Arm.P384.combPk_verified hL }
    P384.Scrub.publicKey_noFrames

/-- `vg_ec_p384_public_key_umaal`, given the group law. -/
theorem publicKeyP384U (hL : Proof.Weierstrass.Law Spec.P384.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.publicKeyP384U
      Proof.EcKey.Arm.P384.combPkSpec 32 :=
  verifiedScrubbed (api := Spec.EcKey.P384.publicKeyApi)
    { code := Impl.Ecdsa.Arm.publicKeyP384CombU
      verified := Proof.EcKey.Arm.P384.combPkU_verified hL }
    P384.Scrub.publicKeyU_noFrames

/-- `vg_ec_p384_compress_public_key`. -/
theorem compressP384 :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.compressP384
      (Spec.EcKey.P384.inst.compressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.P384.inst.compressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.P384.code
      verified := Proof.EcKey.Compressed.Arm.P384.verified }
    P384.Scrub.compress_noFrames

/-- `vg_ec_p384_compress_public_key_umaal`. -/
theorem compressP384U :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.compressP384U
      (Spec.EcKey.P384.inst.compressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.P384.inst.compressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.P384.codeU
      verified := Proof.EcKey.Compressed.Arm.P384.verifiedU }
    P384.Scrub.compressU_noFrames

/-- `vg_ec_p384_decompress_public_key`, given the group law. -/
theorem decompressP384 (hL : Proof.Weierstrass.Law Spec.P384.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.decompressP384
      (Spec.EcKey.P384.inst.decompressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.P384.inst.decompressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.P384Decompress.code
      verified := Proof.EcKey.Compressed.Arm.P384Decompress.verified hL }
    P384.Scrub.decompress_noFrames

/-- `vg_ec_p384_decompress_public_key_umaal`, given the group law. -/
theorem decompressP384U (hL : Proof.Weierstrass.Law Spec.P384.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.decompressP384U
      (Spec.EcKey.P384.inst.decompressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.P384.inst.decompressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.P384Decompress.codeU
      verified := Proof.EcKey.Compressed.Arm.P384Decompress.verifiedU hL }
    P384.Scrub.decompressU_noFrames

end VG.Proof.EcKey.Arm.Fn
