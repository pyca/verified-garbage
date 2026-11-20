module

public import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
public import VerifiedGarbage.Proof.Zeroize.Arm
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.ScrubProved
meta import VerifiedGarbage.Proof.Zeroize.Arm
meta import VerifiedGarbage.Proof.Framework.Lit

/-!
# `vg_zeroize` on ARMv7, as emitted

`vg_zeroize` saves no register and has no frames, so its cleanup
(`Impl.Zeroize.Arm.Fn.zeroize`, `Impl.Residue.Arm.scrub`) sets the registers
a callee may change, and the flags, to constants, and `Fn.zeroize` below
states that it returns without secret residue
(`Arm.Scrub.verifiedScrubbed`), which is what its registration binds. Its
callers (AES-ECB, AES-CBC, ML-KEM) run its code under the internal name
`vg_zeroize_core`, which this leaves as it was.
-/

@[expose] public section

namespace VG.Proof.Zeroize.Arm.Scrub

open VG VG.Arm

theorem zeroize_noFramesArm : Impl.Zeroize.Arm.zeroize.noFrames = true := by lit_decide

end VG.Proof.Zeroize.Arm.Scrub

namespace VG.Proof.Zeroize.Arm.Fn

open VG VG.Arm VG.Arm.Scrub

/-- `vg_zeroize`. -/
theorem zeroize :
    VerifiedScrubbed target Impl.Zeroize.Arm.Fn.zeroize (Spec.Zeroize.zeroizeContract abi) 0 :=
  verifiedScrubbed (api := Spec.Zeroize.zeroizeApi)
    { code := Impl.Zeroize.Arm.zeroize, verified := verified } Scrub.zeroize_noFramesArm

end VG.Proof.Zeroize.Arm.Fn
