module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.Ecdh.P192.ArmFn
public import VerifiedGarbage.Proof.Ecdh.Arm.P192.Verified
public import VerifiedGarbage.Spec.Ecdh.P192
import VerifiedGarbage.Proof.Ecdh.Arm.P192.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.Ecdh.P192.ArmFn
meta import VerifiedGarbage.Proof.Ecdh.Arm.P192.Verified
meta import VerifiedGarbage.Spec.Ecdh.P192
meta import VerifiedGarbage.Proof.Ecdh.Arm.P192.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# ECDH over P-192 on 32-bit ARM, without secret residue

`vg_ecdh_p192`, with either multiplication of the field, has no
frames: it keeps the registers it saves in its scratch space, a buffer
(`Code.noFrames`, evaluated by `lit_decide` on its literal). It is emitted
with its cleanup (`Impl.Ecdh.Arm.Fn`), and `Fn` below has the theorem of each
variant, that it meets its contract and returns without secret residue
(`Arm.Scrub.verifiedScrubbed`), which is what its registration binds.
-/

@[expose] public section

namespace VG.Proof.Ecdh.Arm.P192.Scrub

open VG VG.Arm

theorem exchange_noFrames : Impl.Ecdh.Arm.exchangeP192.noFrames = true := by lit_decide

theorem exchangeU_noFrames : Impl.Ecdh.Arm.exchangeP192U.noFrames = true := by lit_decide

end VG.Proof.Ecdh.Arm.P192.Scrub

namespace VG.Proof.Ecdh.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ecdh_p192`, given the group law. -/
theorem exchangeP192 (hC : Weierstrass.Law Spec.P192.curve) :
    VerifiedScrubbed target Impl.Ecdh.Arm.Fn.exchangeP192
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P192.inst abi) 32 :=
  verifiedScrubbed (api := Spec.Ecdh.P192.exchangeApi)
    { code := Impl.Ecdh.Arm.exchangeP192
      verified := VG.Proof.Ecdh.Arm.P192.ecdh_verified hC }
    VG.Proof.Ecdh.Arm.P192.Scrub.exchange_noFrames

/-- `vg_ecdh_p192_umaal`, given the group law. -/
theorem exchangeP192U (hC : Weierstrass.Law Spec.P192.curve) :
    VerifiedScrubbed target Impl.Ecdh.Arm.Fn.exchangeP192U
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P192.inst abi) 32 :=
  verifiedScrubbed (api := Spec.Ecdh.P192.exchangeApi)
    { code := Impl.Ecdh.Arm.exchangeP192U
      verified := VG.Proof.Ecdh.Arm.P192.ecdhU_verified hC }
    VG.Proof.Ecdh.Arm.P192.Scrub.exchangeU_noFrames

end VG.Proof.Ecdh.Arm.Fn
