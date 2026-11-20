module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.Ecdh.P521.ArmFn
public import VerifiedGarbage.Proof.Ecdh.Arm.P521.Verified
public import VerifiedGarbage.Spec.Ecdh.P521
import VerifiedGarbage.Proof.Ecdh.Arm.P521.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.Ecdh.P521.ArmFn
meta import VerifiedGarbage.Proof.Ecdh.Arm.P521.Verified
meta import VerifiedGarbage.Spec.Ecdh.P521
meta import VerifiedGarbage.Proof.Ecdh.Arm.P521.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# ECDH over P-521 on 32-bit ARM, without secret residue

`vg_ecdh_p521`, with either multiplication of the field, has no
frames: it keeps the registers it saves in its scratch space, a buffer
(`Code.noFrames`, evaluated by `lit_decide` on its literal). It is emitted
with its cleanup (`Impl.Ecdh.Arm.Fn`), and `Fn` below has the theorem of each
variant, that it meets its contract and returns without secret residue
(`Arm.Scrub.verifiedScrubbed`), which is what its registration binds.
-/

@[expose] public section

namespace VG.Proof.Ecdh.Arm.P521.Scrub

open VG VG.Arm

theorem exchange_noFrames : Impl.Ecdh.Arm.exchangeP521.noFrames = true := by lit_decide

theorem exchangeU_noFrames : Impl.Ecdh.Arm.exchangeP521U.noFrames = true := by lit_decide

end VG.Proof.Ecdh.Arm.P521.Scrub

namespace VG.Proof.Ecdh.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ecdh_p521`, given the group law. -/
theorem exchangeP521 (hC : Weierstrass.Law Spec.P521.curve) :
    VerifiedScrubbed target Impl.Ecdh.Arm.Fn.exchangeP521
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst abi) 32 :=
  verifiedScrubbed (api := Spec.Ecdh.P521.exchangeApi)
    { code := Impl.Ecdh.Arm.exchangeP521
      verified := VG.Proof.Ecdh.Arm.P521.ecdh_verified hC }
    VG.Proof.Ecdh.Arm.P521.Scrub.exchange_noFrames

/-- `vg_ecdh_p521_umaal`, given the group law. -/
theorem exchangeP521U (hC : Weierstrass.Law Spec.P521.curve) :
    VerifiedScrubbed target Impl.Ecdh.Arm.Fn.exchangeP521U
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst abi) 32 :=
  verifiedScrubbed (api := Spec.Ecdh.P521.exchangeApi)
    { code := Impl.Ecdh.Arm.exchangeP521U
      verified := VG.Proof.Ecdh.Arm.P521.ecdhU_verified hC }
    VG.Proof.Ecdh.Arm.P521.Scrub.exchangeU_noFrames

end VG.Proof.Ecdh.Arm.Fn
