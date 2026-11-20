module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.Ecdh.P384.ArmFn
public import VerifiedGarbage.Proof.Ecdh.Arm.P384.Verified
public import VerifiedGarbage.Spec.Ecdh.P384
import VerifiedGarbage.Proof.Ecdh.Arm.P384.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.Ecdh.P384.ArmFn
meta import VerifiedGarbage.Proof.Ecdh.Arm.P384.Verified
meta import VerifiedGarbage.Spec.Ecdh.P384
meta import VerifiedGarbage.Proof.Ecdh.Arm.P384.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# ECDH over P-384 on 32-bit ARM, without secret residue

`vg_ecdh_p384`, with either multiplication of the field, has no
frames: it keeps the registers it saves in its scratch space, a buffer
(`Code.noFrames`, evaluated by `lit_decide` on its literal). It is emitted
with its cleanup (`Impl.Ecdh.Arm.Fn`), and `Fn` below has the theorem of each
variant, that it meets its contract and returns without secret residue
(`Arm.Scrub.verifiedScrubbed`), which is what its registration binds.
-/

@[expose] public section

namespace VG.Proof.Ecdh.Arm.P384.Scrub

open VG VG.Arm

theorem exchange_noFrames : Impl.Ecdh.Arm.exchangeP384.noFrames = true := by lit_decide

theorem exchangeU_noFrames : Impl.Ecdh.Arm.exchangeP384U.noFrames = true := by lit_decide

end VG.Proof.Ecdh.Arm.P384.Scrub

namespace VG.Proof.Ecdh.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ecdh_p384`, given the group law. -/
theorem exchangeP384 (hC : Weierstrass.Law Spec.P384.curve) :
    VerifiedScrubbed target Impl.Ecdh.Arm.Fn.exchangeP384
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P384.inst abi) 32 :=
  verifiedScrubbed (api := Spec.Ecdh.P384.exchangeApi)
    { code := Impl.Ecdh.Arm.exchangeP384
      verified := VG.Proof.Ecdh.Arm.P384.ecdh_verified hC }
    VG.Proof.Ecdh.Arm.P384.Scrub.exchange_noFrames

/-- `vg_ecdh_p384_umaal`, given the group law. -/
theorem exchangeP384U (hC : Weierstrass.Law Spec.P384.curve) :
    VerifiedScrubbed target Impl.Ecdh.Arm.Fn.exchangeP384U
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P384.inst abi) 32 :=
  verifiedScrubbed (api := Spec.Ecdh.P384.exchangeApi)
    { code := Impl.Ecdh.Arm.exchangeP384U
      verified := VG.Proof.Ecdh.Arm.P384.ecdhU_verified hC }
    VG.Proof.Ecdh.Arm.P384.Scrub.exchangeU_noFrames

end VG.Proof.Ecdh.Arm.Fn
