module

public import VerifiedGarbage.Impl.Ecdh.P256.Arm
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# ECDH over P-256 on 32-bit ARM, as emitted

`vg_ecdh_p256` and its `_umaal` variant: each one's code, which has
no frames, then the instructions that set the registers a callee may change,
but the result, and the flags to constants (`Impl.Scrub.Arm.scrub`).
-/

@[expose] public section

namespace VG.Impl.Ecdh.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_ecdh_p256`. -/
def exchangeP256 : Prog isa := scrub 32 Impl.Ecdh.Arm.exchangeP256

/-- `vg_ecdh_p256_umaal`. -/
def exchangeP256U : Prog isa := scrub 32 Impl.Ecdh.Arm.exchangeP256U

end VG.Impl.Ecdh.Arm.Fn
