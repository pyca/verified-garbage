module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.EcKey.P521.ArmFn
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.EcKey.Arm.P521.Comb
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P521
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P521Decompress
import VerifiedGarbage.Proof.Ecdsa.Arm.P521.CombLit
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.EcKey.P521.ArmFn
meta import VerifiedGarbage.Proof.Weierstrass.Law
meta import VerifiedGarbage.Proof.EcKey.Arm.P521.Comb
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P521
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.P521Decompress
meta import VerifiedGarbage.Proof.Ecdsa.Arm.P521.CombLit
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# P-521 public keys on 32-bit ARM, without secret residue

`vg_ec_p521_public_key`, `_compress_public_key` and
`_decompress_public_key`, with and without `umaal`, have no frames: they keep
the registers they save in their scratch buffer, and the field functions they
call do too (`Code.noFrames`, evaluated by `lit_decide` on their literals).
Each is emitted with its cleanup (`Impl.EcKey.Arm.Fn`), and `Fn` below has the
theorem of each, that it meets its contract and returns without secret residue
(`Arm.Scrub.verifiedScrubbed`), which is what its registration binds.
-/

@[expose] public section

namespace VG.Proof.EcKey.Arm.P521.Scrub

open VG VG.Arm

theorem publicKey_noFrames : Impl.Ecdsa.Arm.publicKeyP521Comb.noFrames = true := by lit_decide

theorem publicKeyU_noFrames : Impl.Ecdsa.Arm.publicKeyP521CombU.noFrames = true := by lit_decide

theorem compress_noFrames : Proof.EcKey.Compressed.Arm.P521.code.noFrames = true := by lit_decide

theorem compressU_noFrames : Proof.EcKey.Compressed.Arm.P521.codeU.noFrames = true := by lit_decide

theorem decompress_noFrames : Proof.EcKey.Compressed.Arm.P521Decompress.code.noFrames = true := by lit_decide

theorem decompressU_noFrames : Proof.EcKey.Compressed.Arm.P521Decompress.codeU.noFrames = true := by lit_decide

end VG.Proof.EcKey.Arm.P521.Scrub

namespace VG.Proof.EcKey.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ec_p521_public_key`, given the group law. -/
theorem publicKeyP521 (hL : Proof.Weierstrass.Law Spec.P521.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.publicKeyP521
      Proof.EcKey.Arm.P521.combPkSpec 32 :=
  verifiedScrubbed (api := Spec.EcKey.P521.publicKeyApi)
    { code := Impl.Ecdsa.Arm.publicKeyP521Comb
      verified := Proof.EcKey.Arm.P521.combPk_verified hL }
    P521.Scrub.publicKey_noFrames

/-- `vg_ec_p521_public_key_umaal`, given the group law. -/
theorem publicKeyP521U (hL : Proof.Weierstrass.Law Spec.P521.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.publicKeyP521U
      Proof.EcKey.Arm.P521.combPkSpec 32 :=
  verifiedScrubbed (api := Spec.EcKey.P521.publicKeyApi)
    { code := Impl.Ecdsa.Arm.publicKeyP521CombU
      verified := Proof.EcKey.Arm.P521.combPkU_verified hL }
    P521.Scrub.publicKeyU_noFrames

/-- `vg_ec_p521_compress_public_key`. -/
theorem compressP521 :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.compressP521
      (Spec.EcKey.P521.inst.compressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.P521.inst.compressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.P521.code
      verified := Proof.EcKey.Compressed.Arm.P521.verified }
    P521.Scrub.compress_noFrames

/-- `vg_ec_p521_compress_public_key_umaal`. -/
theorem compressP521U :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.compressP521U
      (Spec.EcKey.P521.inst.compressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.P521.inst.compressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.P521.codeU
      verified := Proof.EcKey.Compressed.Arm.P521.verifiedU }
    P521.Scrub.compressU_noFrames

/-- `vg_ec_p521_decompress_public_key`, given the group law. -/
theorem decompressP521 (hL : Proof.Weierstrass.Law Spec.P521.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.decompressP521
      (Spec.EcKey.P521.inst.decompressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.P521.inst.decompressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.P521Decompress.code
      verified := Proof.EcKey.Compressed.Arm.P521Decompress.verified hL }
    P521.Scrub.decompress_noFrames

/-- `vg_ec_p521_decompress_public_key_umaal`, given the group law. -/
theorem decompressP521U (hL : Proof.Weierstrass.Law Spec.P521.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.decompressP521U
      (Spec.EcKey.P521.inst.decompressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.P521.inst.decompressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.P521Decompress.codeU
      verified := Proof.EcKey.Compressed.Arm.P521Decompress.verifiedU hL }
    P521.Scrub.decompressU_noFrames

end VG.Proof.EcKey.Arm.Fn
