module

public import VerifiedGarbage.Proof.Framework.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Zeroize.Arm
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Scrub
meta import VerifiedGarbage.Proof.Framework.Registration
meta import VerifiedGarbage.Proof.Zeroize.Arm
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_zeroize` on ARMv7, without secret residue

`vg_zeroize` saves no register and has no frames, so it is registered
scrubbed (`Arm.Scrub.scrubReg`): followed by instructions that set the
registers a callee may change, and the flags, to constants. Its callers
(AES-ECB, AES-CBC, ML-KEM) run its code under the internal name
`vg_zeroize_core`, which this leaves as it was.
-/

@[expose] public section

namespace VG.Proof.Zeroize.Arm.Scrub

open VG VG.Arm

theorem zeroize_noFramesArm : Impl.Zeroize.Arm.zeroize.noFrames = true := by lit_decide

/-- `Spec.Zeroize.zeroizeApi`, with the registers it may change cleared on
return. -/
def zeroizeRegArm : Registration Spec.Zeroize.zeroizeApi target :=
  Arm.Scrub.scrubReg { code := Impl.Zeroize.Arm.zeroize, verified := verified }
    zeroize_noFramesArm

end VG.Proof.Zeroize.Arm.Scrub
