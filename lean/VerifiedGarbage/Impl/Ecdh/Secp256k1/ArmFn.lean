module

public import VerifiedGarbage.Impl.Ecdh.Secp256k1.Arm
public import VerifiedGarbage.Impl.Scrub.Arm

/-!
# ECDH over secp256k1 on 32-bit ARM, as emitted

`vg_ecdh_secp256k1` and its `_umaal` variant: each one's code, which has
no frames, then the instructions that set the registers a callee may change,
but the result, and the flags to constants (`Impl.Scrub.Arm.scrub`).
-/

@[expose] public section

namespace VG.Impl.Ecdh.Arm.Fn

open VG.Arm VG.Impl.Scrub.Arm

/-- `vg_ecdh_secp256k1`. -/
def exchangeSecp256k1 : Prog isa := scrub 32 Impl.Ecdh.Arm.exchangeSecp256k1

/-- `vg_ecdh_secp256k1_umaal`. -/
def exchangeSecp256k1U : Prog isa := scrub 32 Impl.Ecdh.Arm.exchangeSecp256k1U

end VG.Impl.Ecdh.Arm.Fn
