module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.EcKey.BrainpoolP320r1.ArmFn
public import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP320r1.Comb
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.BrainpoolP320r1
public import VerifiedGarbage.Proof.EcKey.Compressed.Arm.BrainpoolP320r1Decompress
import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP320r1.CombLit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.EcKey.BrainpoolP320r1.ArmFn
meta import VerifiedGarbage.Proof.EcKey.Arm.BrainpoolP320r1.Comb
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.BrainpoolP320r1
meta import VerifiedGarbage.Proof.EcKey.Compressed.Arm.BrainpoolP320r1Decompress
meta import VerifiedGarbage.Proof.Ecdsa.Arm.BrainpoolP320r1.CombLit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# brainpoolP320r1 public keys on 32-bit ARM, without secret residue

`vg_ec_brainpoolp320r1_public_key`, `_compress_public_key` and
`_decompress_public_key`, with and without `umaal`, have no frames: they keep
the registers they save in their scratch buffer, and the field functions they
call do too (`Code.noFrames`, evaluated by `lit_decide` on their literals).
Each is emitted with its cleanup (`Impl.EcKey.Arm.Fn`), and `Fn` below has the
theorem of each, that it meets its contract and returns without secret residue
(`Arm.Scrub.verifiedScrubbed`), which is what its registration binds.
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

end VG.Proof.EcKey.Arm.BrainpoolP320r1.Scrub

namespace VG.Proof.EcKey.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ec_brainpoolp320r1_public_key`, given the group law. -/
theorem publicKeyBrainpoolP320r1 (hL : Proof.Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.publicKeyBrainpoolP320r1
      Proof.EcKey.Arm.BrainpoolP320r1.combPkSpec 32 :=
  verifiedScrubbed (api := Spec.EcKey.BrainpoolP320r1.publicKeyApi)
    { code := Impl.Ecdsa.Arm.publicKeyBrainpoolP320r1Comb
      verified := Proof.EcKey.Arm.BrainpoolP320r1.combPk_verified hL }
    BrainpoolP320r1.Scrub.publicKey_noFrames

/-- `vg_ec_brainpoolp320r1_public_key_umaal`, given the group law. -/
theorem publicKeyBrainpoolP320r1U (hL : Proof.Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.publicKeyBrainpoolP320r1U
      Proof.EcKey.Arm.BrainpoolP320r1.combPkSpec 32 :=
  verifiedScrubbed (api := Spec.EcKey.BrainpoolP320r1.publicKeyApi)
    { code := Impl.Ecdsa.Arm.publicKeyBrainpoolP320r1CombU
      verified := Proof.EcKey.Arm.BrainpoolP320r1.combPkU_verified hL }
    BrainpoolP320r1.Scrub.publicKeyU_noFrames

/-- `vg_ec_brainpoolp320r1_compress_public_key`. -/
theorem compressBrainpoolP320r1 :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.compressBrainpoolP320r1
      (Spec.EcKey.BrainpoolP320r1.inst.compressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.BrainpoolP320r1.inst.compressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.BrainpoolP320r1.code
      verified := Proof.EcKey.Compressed.Arm.BrainpoolP320r1.verified }
    BrainpoolP320r1.Scrub.compress_noFrames

/-- `vg_ec_brainpoolp320r1_compress_public_key_umaal`. -/
theorem compressBrainpoolP320r1U :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.compressBrainpoolP320r1U
      (Spec.EcKey.BrainpoolP320r1.inst.compressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.BrainpoolP320r1.inst.compressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.BrainpoolP320r1.codeU
      verified := Proof.EcKey.Compressed.Arm.BrainpoolP320r1.verifiedU }
    BrainpoolP320r1.Scrub.compressU_noFrames

/-- `vg_ec_brainpoolp320r1_decompress_public_key`, given the group law. -/
theorem decompressBrainpoolP320r1 (hL : Proof.Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.decompressBrainpoolP320r1
      (Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.BrainpoolP320r1Decompress.code
      verified := Proof.EcKey.Compressed.Arm.BrainpoolP320r1Decompress.verified hL }
    BrainpoolP320r1.Scrub.decompress_noFrames

/-- `vg_ec_brainpoolp320r1_decompress_public_key_umaal`, given the group law. -/
theorem decompressBrainpoolP320r1U (hL : Proof.Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    VerifiedScrubbed target Impl.EcKey.Arm.Fn.decompressBrainpoolP320r1U
      (Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyContract abi 0) 32 :=
  verifiedScrubbed (api := Spec.EcKey.BrainpoolP320r1.inst.decompressPublicKeyApi)
    { code := Proof.EcKey.Compressed.Arm.BrainpoolP320r1Decompress.codeU
      verified := Proof.EcKey.Compressed.Arm.BrainpoolP320r1Decompress.verifiedU hL }
    BrainpoolP320r1.Scrub.decompressU_noFrames

end VG.Proof.EcKey.Arm.Fn
