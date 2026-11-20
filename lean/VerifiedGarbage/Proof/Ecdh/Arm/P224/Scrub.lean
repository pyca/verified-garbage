module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.Ecdh.P224.ArmFn
public import VerifiedGarbage.Proof.Ecdh.Arm.P224.Verified
public import VerifiedGarbage.Spec.Ecdh.P224
import VerifiedGarbage.Proof.Ecdh.Arm.P224.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.Ecdh.P224.ArmFn
meta import VerifiedGarbage.Proof.Ecdh.Arm.P224.Verified
meta import VerifiedGarbage.Spec.Ecdh.P224
meta import VerifiedGarbage.Proof.Ecdh.Arm.P224.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# ECDH over P-224 on 32-bit ARM, without secret residue

`vg_ecdh_p224`, with either multiplication of the field, has no
frames: it keeps the registers it saves in its scratch space, a buffer
(`Code.noFrames`, evaluated by `lit_decide` on its literal). It is emitted
with its cleanup (`Impl.Ecdh.Arm.Fn`), and `Fn` below has the theorem of each
variant, that it meets its contract and returns without secret residue
(`Arm.Scrub.verifiedScrubbed`), which is what its registration binds.
-/

@[expose] public section

namespace VG.Proof.Ecdh.Arm.P224.Scrub

open VG VG.Arm

theorem exchange_noFrames : Impl.Ecdh.Arm.exchangeP224.noFrames = true := by lit_decide

theorem exchangeU_noFrames : Impl.Ecdh.Arm.exchangeP224U.noFrames = true := by lit_decide

end VG.Proof.Ecdh.Arm.P224.Scrub

namespace VG.Proof.Ecdh.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ecdh_p224`, given the group law. -/
theorem exchangeP224 (hC : Weierstrass.Law Spec.P224.curve) :
    VerifiedScrubbed target Impl.Ecdh.Arm.Fn.exchangeP224
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P224.inst abi) 32 :=
  verifiedScrubbed (api := Spec.Ecdh.P224.exchangeApi)
    { code := Impl.Ecdh.Arm.exchangeP224
      verified := VG.Proof.Ecdh.Arm.P224.ecdh_verified hC }
    VG.Proof.Ecdh.Arm.P224.Scrub.exchange_noFrames

/-- `vg_ecdh_p224_umaal`, given the group law. -/
theorem exchangeP224U (hC : Weierstrass.Law Spec.P224.curve) :
    VerifiedScrubbed target Impl.Ecdh.Arm.Fn.exchangeP224U
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P224.inst abi) 32 :=
  verifiedScrubbed (api := Spec.Ecdh.P224.exchangeApi)
    { code := Impl.Ecdh.Arm.exchangeP224U
      verified := VG.Proof.Ecdh.Arm.P224.ecdhU_verified hC }
    VG.Proof.Ecdh.Arm.P224.Scrub.exchangeU_noFrames

end VG.Proof.Ecdh.Arm.Fn
