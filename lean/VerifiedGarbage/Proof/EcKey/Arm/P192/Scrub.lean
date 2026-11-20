module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.EcKey.P192.ArmFn
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.EcKey.Arm.P192.Comb
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P192
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P192Decompress
import VerifiedGarbage.Proof.Ecdsa.Arm.P192.CombLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.EcKey.P192.ArmFn
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.EcKey.Arm.P192.Comb
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P192
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P192Decompress
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P192.CombLit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# P-192 public keys on 32-bit ARM, without secret residue

`vg_ec_p192_public_key`, `_compress_public_key` and
`_decompress_public_key`, with and without `umaal`, have no frames: they keep
the registers they save in their scratch buffer, and the field functions they
call do too (`Code.noFrames`, evaluated by `lit_decide` on their literals).
Each is emitted with its cleanup (`Impl.EcKey.Arm.Fn`), and `Fn` below has the
theorem of each, that it meets its contract and returns without secret residue
(`Arm.Scrub.verifiedScrubbed`), which is what its registration binds.
-/

@[expose] public section

namespace VG.Proof.EcKey.Arm.P192.Scrub

open VG VG.Arm

theorem publicKey_noFrames : Impl.Ecdsa.Arm.publicKeyP192Comb.noFrames = true := by lit_decide

theorem publicKeyU_noFrames : Impl.Ecdsa.Arm.publicKeyP192CombU.noFrames = true := by lit_decide

theorem compress_noFrames : Proof.EcKey.Compressed.Arm.P192.code.noFrames = true := by lit_decide

theorem compressU_noFrames : Proof.EcKey.Compressed.Arm.P192.codeU.noFrames = true := by lit_decide

theorem decompress_noFrames : Proof.EcKey.Compressed.Arm.P192Decompress.code.noFrames = true := by lit_decide

theorem decompressU_noFrames : Proof.EcKey.Compressed.Arm.P192Decompress.codeU.noFrames = true := by lit_decide

end VG.Proof.EcKey.Arm.P192.Scrub

namespace VG.Proof.EcKey.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ec_p192_public_key`, given the group law. -/
theorem publicKeyP192 (hL : Proof.Weierstrass.Law Spec.P192.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.publicKeyP192
      Proof.EcKey.Arm.P192.combPkSpec 32 :=
  verifiedScrubbed (api := Spec.EcKey.P192.publicKeyApi)
    { code := Impl.Ecdsa.Arm.publicKeyP192Comb
      verified := Proof.EcKey.Arm.P192.combPk_verified hL }
    P192.Scrub.publicKey_noFrames

/-- `vg_ec_p192_public_key_umaal`, given the group law. -/
theorem publicKeyP192U (hL : Proof.Weierstrass.Law Spec.P192.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.publicKeyP192U
      Proof.EcKey.Arm.P192.combPkSpec 32 :=
  verifiedScrubbed (api := Spec.EcKey.P192.publicKeyApi)
    { code := Impl.Ecdsa.Arm.publicKeyP192CombU
      verified := Proof.EcKey.Arm.P192.combPkU_verified hL }
    P192.Scrub.publicKeyU_noFrames

/-- `vg_ec_p192_compress_public_key`. -/
theorem compressP192 :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.compressP192
      (Spec.EcKey.P192.inst.compressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.P192.inst.compressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.P192.code
      verified := Proof.EcKey.Compressed.Arm.P192.verified }
    P192.Scrub.compress_noFrames

/-- `vg_ec_p192_compress_public_key_umaal`. -/
theorem compressP192U :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.compressP192U
      (Spec.EcKey.P192.inst.compressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.P192.inst.compressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.P192.codeU
      verified := Proof.EcKey.Compressed.Arm.P192.verifiedU }
    P192.Scrub.compressU_noFrames

/-- `vg_ec_p192_decompress_public_key`, given the group law. -/
theorem decompressP192 (hL : Proof.Weierstrass.Law Spec.P192.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.decompressP192
      (Spec.EcKey.P192.inst.decompressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.P192.inst.decompressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.P192Decompress.code
      verified := Proof.EcKey.Compressed.Arm.P192Decompress.verified hL }
    P192.Scrub.decompress_noFrames

/-- `vg_ec_p192_decompress_public_key_umaal`, given the group law. -/
theorem decompressP192U (hL : Proof.Weierstrass.Law Spec.P192.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.decompressP192U
      (Spec.EcKey.P192.inst.decompressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.P192.inst.decompressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.P192Decompress.codeU
      verified := Proof.EcKey.Compressed.Arm.P192Decompress.verifiedU hL }
    P192.Scrub.decompressU_noFrames

end VG.Proof.EcKey.Arm.Fn
