module

public import VerifiedGarbage.Impl.Ecdh.Arm
public import VerifiedGarbage.Impl.Ecdsa.P521.Arm

/-! # ECDH over P-521 on 32-bit ARM: nine-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.Arm

open VG.Arm

/-- `vg_ecdh_p521`, or with `u` `vg_ecdh_p521_umaal`. -/
def exchangeP521With (u : Bool) : Prog isa := Cfg.exchange (Impl.Ecdsa.Arm.p521With u)

/-- `vg_ecdh_p521`. -/
def exchangeP521 : Prog isa := exchangeP521With false

/-- `vg_ecdh_p521_umaal`. -/
def exchangeP521U : Prog isa := exchangeP521With true

end VG.Impl.Ecdh.Arm
