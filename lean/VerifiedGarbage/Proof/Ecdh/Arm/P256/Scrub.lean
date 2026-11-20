module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.Ecdh.P256.ArmFn
public import VerifiedGarbage.Proof.Ecdh.Arm.Verified
public import VerifiedGarbage.Spec.Ecdh.P256
import VerifiedGarbage.Proof.Ecdh.Arm.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.Ecdh.P256.ArmFn
meta import VerifiedGarbage.Proof.Ecdh.Arm.Verified
meta import VerifiedGarbage.Spec.Ecdh.P256
meta import VerifiedGarbage.Proof.Ecdh.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# ECDH over P-256 on 32-bit ARM, without secret residue

`vg_ecdh_p256`, with either multiplication of the field, has no
frames: it keeps the registers it saves in its scratch space, a buffer
(`Code.noFrames`, evaluated by `lit_decide` on its literal). It is emitted
with its cleanup (`Impl.Ecdh.Arm.Fn`), and `Fn` below has the theorem of each
variant, that it meets its contract and returns without secret residue
(`Arm.Scrub.verifiedScrubbed`), which is what its registration binds.
-/

@[expose] public section

namespace VG.Proof.Ecdh.Arm.P256.Scrub

open VG VG.Arm

theorem exchange_noFrames : Impl.Ecdh.Arm.exchangeP256.noFrames = true := by lit_decide

theorem exchangeU_noFrames : Impl.Ecdh.Arm.exchangeP256U.noFrames = true := by lit_decide

end VG.Proof.Ecdh.Arm.P256.Scrub

namespace VG.Proof.Ecdh.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ecdh_p256`, given the group law. -/
theorem exchangeP256 (hC : Weierstrass.Law Spec.P256.curve) :
    VerifiedScrubbed target Impl.Ecdh.Arm.Fn.exchangeP256
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst abi) 32 :=
  verifiedScrubbed (api := Spec.Ecdh.P256.exchangeApi)
    { code := Impl.Ecdh.Arm.exchangeP256
      verified := VG.Proof.Ecdh.Arm.ecdh_verified hC }
    VG.Proof.Ecdh.Arm.P256.Scrub.exchange_noFrames

/-- `vg_ecdh_p256_umaal`, given the group law. -/
theorem exchangeP256U (hC : Weierstrass.Law Spec.P256.curve) :
    VerifiedScrubbed target Impl.Ecdh.Arm.Fn.exchangeP256U
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P256.inst abi) 32 :=
  verifiedScrubbed (api := Spec.Ecdh.P256.exchangeApi)
    { code := Impl.Ecdh.Arm.exchangeP256U
      verified := VG.Proof.Ecdh.Arm.ecdhU_verified hC }
    VG.Proof.Ecdh.Arm.P256.Scrub.exchangeU_noFrames

end VG.Proof.Ecdh.Arm.Fn
