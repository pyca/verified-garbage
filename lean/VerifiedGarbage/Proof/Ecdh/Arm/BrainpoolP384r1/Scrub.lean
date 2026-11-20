module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.ArmFn
public import VerifiedGarbage.Proof.Ecdh.Arm.BrainpoolP384r1.Verified
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP384r1
import VerifiedGarbage.Proof.Ecdh.Arm.BrainpoolP384r1.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Impl.Ecdh.BrainpoolP384r1.ArmFn
meta import VerifiedGarbage.Proof.Ecdh.Arm.BrainpoolP384r1.Verified
meta import VerifiedGarbage.Spec.Ecdh.BrainpoolP384r1
meta import VerifiedGarbage.Proof.Ecdh.Arm.BrainpoolP384r1.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# ECDH over brainpoolP384r1 on 32-bit ARM, without secret residue

`vg_ecdh_brainpoolp384r1`, with either multiplication of the field, has no
frames: it keeps the registers it saves in its scratch space, a buffer
(`Code.noFrames`, evaluated by `lit_decide` on its literal). It is emitted
with its cleanup (`Impl.Ecdh.Arm.Fn`), and `Fn` below has the theorem of each
variant, that it meets its contract and returns without secret residue
(`Arm.Scrub.verifiedScrubbed`), which is what its registration binds.
-/

@[expose] public section

namespace VG.Proof.Ecdh.Arm.BrainpoolP384r1.Scrub

open VG VG.Arm

theorem exchange_noFrames : Impl.Ecdh.Arm.exchangeBrainpoolP384r1.noFrames = true := by lit_decide

theorem exchangeU_noFrames : Impl.Ecdh.Arm.exchangeBrainpoolP384r1U.noFrames = true := by lit_decide

end VG.Proof.Ecdh.Arm.BrainpoolP384r1.Scrub

namespace VG.Proof.Ecdh.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_ecdh_brainpoolp384r1`, given the group law. -/
theorem exchangeBrainpoolP384r1 (hC : Weierstrass.Law Spec.BrainpoolP384r1.curve) :
    VerifiedScrubbed target Impl.Ecdh.Arm.Fn.exchangeBrainpoolP384r1
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.BrainpoolP384r1.inst abi) 32 :=
  verifiedScrubbed (api := Spec.Ecdh.BrainpoolP384r1.exchangeApi)
    { code := Impl.Ecdh.Arm.exchangeBrainpoolP384r1
      verified := VG.Proof.Ecdh.Arm.BrainpoolP384r1.ecdh_verified hC }
    VG.Proof.Ecdh.Arm.BrainpoolP384r1.Scrub.exchange_noFrames

/-- `vg_ecdh_brainpoolp384r1_umaal`, given the group law. -/
theorem exchangeBrainpoolP384r1U (hC : Weierstrass.Law Spec.BrainpoolP384r1.curve) :
    VerifiedScrubbed target Impl.Ecdh.Arm.Fn.exchangeBrainpoolP384r1U
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.BrainpoolP384r1.inst abi) 32 :=
  verifiedScrubbed (api := Spec.Ecdh.BrainpoolP384r1.exchangeApi)
    { code := Impl.Ecdh.Arm.exchangeBrainpoolP384r1U
      verified := VG.Proof.Ecdh.Arm.BrainpoolP384r1.ecdhU_verified hC }
    VG.Proof.Ecdh.Arm.BrainpoolP384r1.Scrub.exchangeU_noFrames

end VG.Proof.Ecdh.Arm.Fn
