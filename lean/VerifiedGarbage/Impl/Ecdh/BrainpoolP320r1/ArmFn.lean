module

public import VerifiedGarbage.Impl.Ecdh.BrainpoolP320r1.Arm
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# ECDH over brainpoolP320r1 on 32-bit ARM, as emitted

`vg_ecdh_brainpoolp320r1` and its `_umaal` variant: each one's code, which has
no frames, then the instructions that set the registers a callee may change,
but the result, and the flags to constants (`Impl.Scrub.Arm.scrub`).
-/

@[expose] public section

namespace VG.Impl.Ecdh.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_ecdh_brainpoolp320r1`. -/
def exchangeBrainpoolP320r1 : Prog isa := scrub 32 Impl.Ecdh.Arm.exchangeBrainpoolP320r1

/-- `vg_ecdh_brainpoolp320r1_umaal`. -/
def exchangeBrainpoolP320r1U : Prog isa := scrub 32 Impl.Ecdh.Arm.exchangeBrainpoolP320r1U

end VG.Impl.Ecdh.Arm.Fn
