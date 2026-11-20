module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.Ecdh.Secp256k1.ArmFn
public import VerifiedGarbage.Proof.Ecdh.Arm.Secp256k1.Verified
public import VerifiedGarbage.Spec.Ecdh.Secp256k1
import VerifiedGarbage.Proof.Ecdh.Arm.Secp256k1.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.Ecdh.Secp256k1.ArmFn
meta import VerifiedGarbage.Proof.Ecdh.Arm.Secp256k1.Verified
meta import VerifiedGarbage.Spec.Ecdh.Secp256k1
meta import VerifiedGarbage.Proof.Ecdh.Arm.Secp256k1.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# ECDH over secp256k1 on 32-bit ARM, without secret residue

`vg_ecdh_secp256k1`, with either multiplication of the field, has no
frames: it keeps the registers it saves in its scratch space, a buffer
(`Code.noFrames`, evaluated by `lit_decide` on its literal). It is emitted
with its cleanup (`Impl.Ecdh.Arm.Fn`), and `Fn` below has the theorem of each
variant, that it meets its contract and returns without secret residue
(`Arm.Scrub.verifiedScrubbed`), which is what its registration binds.
-/

@[expose] public section

namespace VG.Proof.Ecdh.Arm.Secp256k1.Scrub

open VG VG.Arm

theorem exchange_noFrames : Impl.Ecdh.Arm.exchangeSecp256k1.noFrames = true := by lit_decide

theorem exchangeU_noFrames : Impl.Ecdh.Arm.exchangeSecp256k1U.noFrames = true := by lit_decide

end VG.Proof.Ecdh.Arm.Secp256k1.Scrub

namespace VG.Proof.Ecdh.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ecdh_secp256k1`, given the group law. -/
theorem exchangeSecp256k1 (hC : Weierstrass.Law Spec.Secp256k1.curve) :
    VerifiedScrubbed target Impl.Ecdh.Arm.Fn.exchangeSecp256k1
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.Secp256k1.inst abi) 32 :=
  verifiedScrubbed (api := Spec.Ecdh.Secp256k1.exchangeApi)
    { code := Impl.Ecdh.Arm.exchangeSecp256k1
      verified := VG.Proof.Ecdh.Arm.Secp256k1.ecdh_verified hC }
    VG.Proof.Ecdh.Arm.Secp256k1.Scrub.exchange_noFrames

/-- `vg_ecdh_secp256k1_umaal`, given the group law. -/
theorem exchangeSecp256k1U (hC : Weierstrass.Law Spec.Secp256k1.curve) :
    VerifiedScrubbed target Impl.Ecdh.Arm.Fn.exchangeSecp256k1U
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.Secp256k1.inst abi) 32 :=
  verifiedScrubbed (api := Spec.Ecdh.Secp256k1.exchangeApi)
    { code := Impl.Ecdh.Arm.exchangeSecp256k1U
      verified := VG.Proof.Ecdh.Arm.Secp256k1.ecdhU_verified hC }
    VG.Proof.Ecdh.Arm.Secp256k1.Scrub.exchangeU_noFrames

end VG.Proof.Ecdh.Arm.Fn
