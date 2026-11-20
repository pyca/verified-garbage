module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.EcKey.P224.ArmFn
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.EcKey.Arm.P224.Comb
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P224
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P224Decompress
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.CombLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.EcKey.P224.ArmFn
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.EcKey.Arm.P224.Comb
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P224
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P224Decompress
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P224.CombLit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# P-224 public keys on 32-bit ARM, without secret residue

`vg_ec_p224_public_key`, `_compress_public_key` and
`_decompress_public_key`, with and without `umaal`, have no frames: they keep
the registers they save in their scratch buffer, and the field functions they
call do too (`Code.noFrames`, evaluated by `lit_decide` on their literals).
Each is emitted with its cleanup (`Impl.EcKey.Arm.Fn`), and `Fn` below has the
theorem of each, that it meets its contract and returns without secret residue
(`Arm.Scrub.verifiedScrubbed`), which is what its registration binds.
-/

@[expose] public section

namespace VG.Proof.EcKey.Arm.P224.Scrub

open VG VG.Arm

theorem publicKey_noFrames : Impl.Ecdsa.Arm.publicKeyP224Comb.noFrames = true := by lit_decide

theorem publicKeyU_noFrames : Impl.Ecdsa.Arm.publicKeyP224CombU.noFrames = true := by lit_decide

theorem compress_noFrames : Proof.EcKey.Compressed.Arm.P224.code.noFrames = true := by lit_decide

theorem compressU_noFrames : Proof.EcKey.Compressed.Arm.P224.codeU.noFrames = true := by lit_decide

theorem decompress_noFrames : Proof.EcKey.Compressed.Arm.P224Decompress.code.noFrames = true := by lit_decide

theorem decompressU_noFrames : Proof.EcKey.Compressed.Arm.P224Decompress.codeU.noFrames = true := by lit_decide

end VG.Proof.EcKey.Arm.P224.Scrub

namespace VG.Proof.EcKey.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ec_p224_public_key`, given the group law. -/
theorem publicKeyP224 (hL : Proof.Weierstrass.Law Spec.P224.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.publicKeyP224
      Proof.EcKey.Arm.P224.combPkSpec 32 :=
  verifiedScrubbed (api := Spec.EcKey.P224.publicKeyApi)
    { code := Impl.Ecdsa.Arm.publicKeyP224Comb
      verified := Proof.EcKey.Arm.P224.combPk_verified hL }
    P224.Scrub.publicKey_noFrames

/-- `vg_ec_p224_public_key_umaal`, given the group law. -/
theorem publicKeyP224U (hL : Proof.Weierstrass.Law Spec.P224.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.publicKeyP224U
      Proof.EcKey.Arm.P224.combPkSpec 32 :=
  verifiedScrubbed (api := Spec.EcKey.P224.publicKeyApi)
    { code := Impl.Ecdsa.Arm.publicKeyP224CombU
      verified := Proof.EcKey.Arm.P224.combPkU_verified hL }
    P224.Scrub.publicKeyU_noFrames

/-- `vg_ec_p224_compress_public_key`. -/
theorem compressP224 :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.compressP224
      (Spec.EcKey.P224.inst.compressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.P224.inst.compressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.P224.code
      verified := Proof.EcKey.Compressed.Arm.P224.verified }
    P224.Scrub.compress_noFrames

/-- `vg_ec_p224_compress_public_key_umaal`. -/
theorem compressP224U :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.compressP224U
      (Spec.EcKey.P224.inst.compressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.P224.inst.compressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.P224.codeU
      verified := Proof.EcKey.Compressed.Arm.P224.verifiedU }
    P224.Scrub.compressU_noFrames

/-- `vg_ec_p224_decompress_public_key`, given the group law. -/
theorem decompressP224 (hL : Proof.Weierstrass.Law Spec.P224.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.decompressP224
      (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.P224.inst.decompressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.P224Decompress.code
      verified := Proof.EcKey.Compressed.Arm.P224Decompress.verified hL }
    P224.Scrub.decompress_noFrames

/-- `vg_ec_p224_decompress_public_key_umaal`, given the group law. -/
theorem decompressP224U (hL : Proof.Weierstrass.Law Spec.P224.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.decompressP224U
      (Spec.EcKey.P224.inst.decompressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.P224.inst.decompressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.P224Decompress.codeU
      verified := Proof.EcKey.Compressed.Arm.P224Decompress.verifiedU hL }
    P224.Scrub.decompressU_noFrames

end VG.Proof.EcKey.Arm.Fn
