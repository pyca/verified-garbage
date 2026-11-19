module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ecdh.Arm.BrainpoolP320r1.Verified
public import VerifiedGarbage.Spec.Ecdh.BrainpoolP320r1
import VerifiedGarbage.Proof.Ecdh.Arm.BrainpoolP320r1.Lit
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Ecdh.Arm.BrainpoolP320r1.Verified
meta import VerifiedGarbage.Spec.Ecdh.BrainpoolP320r1
meta import VerifiedGarbage.Proof.Ecdh.Arm.BrainpoolP320r1.Lit
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# ECDH over brainpoolP320r1 on 32-bit ARM, without secret residue

`vg_ecdh_brainpoolp320r1`, with either multiplication of the field, has no
frames: it keeps the registers it saves in its scratch space, a buffer. It is
registered scrubbed (`Arm.Scrub.scrubReg`): followed by instructions that set
the registers a callee may change, but the result, and the flags to constants.
-/

@[expose] public section

namespace VG.Proof.Ecdh.Arm.BrainpoolP320r1.Scrub

open VG VG.Arm

theorem exchange_noFrames : Impl.Ecdh.Arm.exchangeBrainpoolP320r1.noFrames = true := by lit_decide

theorem exchangeU_noFrames : Impl.Ecdh.Arm.exchangeBrainpoolP320r1U.noFrames = true := by lit_decide

/-- `vg_ecdh_brainpoolp320r1`, given the group law. -/
def exchangeReg (hC : Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    Registration Spec.Ecdh.BrainpoolP320r1.exchangeApi target :=
  Arm.Scrub.scrubReg {
      code := Impl.Ecdh.Arm.exchangeBrainpoolP320r1
      verified := ecdh_verified hC }
    exchange_noFrames

/-- `vg_ecdh_brainpoolp320r1_umaal`, given the group law. -/
def exchangeUReg (hC : Weierstrass.Law Spec.BrainpoolP320r1.curve) :
    Registration Spec.Ecdh.BrainpoolP320r1.exchangeApi target :=
  Arm.Scrub.scrubReg {
      suffix := "_umaal"
      code := Impl.Ecdh.Arm.exchangeBrainpoolP320r1U
      verified := ecdhU_verified hC }
    exchangeU_noFrames

end VG.Proof.Ecdh.Arm.BrainpoolP320r1.Scrub
