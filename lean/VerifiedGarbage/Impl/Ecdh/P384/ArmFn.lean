module

public import VerifiedGarbage.Impl.Ecdh.P384.Arm
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# ECDH over P-384 on 32-bit ARM, as emitted

`vg_ecdh_p384` and its `_umaal` variant: each one's code, which has
no frames, then the instructions that set the registers a callee may change,
but the result, and the flags to constants (`Impl.Scrub.Arm.scrub`).
-/

@[expose] public section

namespace VG.Impl.Ecdh.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_ecdh_p384`. -/
def exchangeP384 : Prog isa := scrub 32 Impl.Ecdh.Arm.exchangeP384

/-- `vg_ecdh_p384_umaal`. -/
def exchangeP384U : Prog isa := scrub 32 Impl.Ecdh.Arm.exchangeP384U

end VG.Impl.Ecdh.Arm.Fn
