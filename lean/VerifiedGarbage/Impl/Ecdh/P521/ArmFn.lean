module

public import VerifiedGarbage.Impl.Ecdh.P521.Arm
public import VerifiedGarbage.Impl.Residue.Arm

/-!
# ECDH over P-521 on 32-bit ARM, as emitted

`vg_ecdh_p521` and its `_umaal` variant: each one's code, which has
no frames, then the instructions that set the registers a callee may change,
but the result, and the flags to constants (`Impl.Residue.Arm.scrub`).
-/

@[expose] public section

namespace VG.Impl.Ecdh.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_ecdh_p521`. -/
def exchangeP521 : Prog isa := scrub 32 Impl.Ecdh.Arm.exchangeP521

/-- `vg_ecdh_p521_umaal`. -/
def exchangeP521U : Prog isa := scrub 32 Impl.Ecdh.Arm.exchangeP521U

end VG.Impl.Ecdh.Arm.Fn
