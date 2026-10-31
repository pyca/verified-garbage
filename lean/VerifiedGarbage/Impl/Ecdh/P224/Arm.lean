module

public import VerifiedGarbage.Impl.Ecdh.Arm
public import VerifiedGarbage.Impl.Ecdsa.P224.Arm

/-! # ECDH over P-224 on 32-bit ARM: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.Arm

open VG.Arm

/-- `vg_ecdh_p224`, or with `u` `vg_ecdh_p224_umaal`. -/
def exchangeP224With (u : Bool) : Prog isa := Cfg.exchange (Impl.Ecdsa.Arm.p224With u)

/-- `vg_ecdh_p224`. -/
def exchangeP224 : Prog isa := exchangeP224With false

/-- `vg_ecdh_p224_umaal`. -/
def exchangeP224U : Prog isa := exchangeP224With true

end VG.Impl.Ecdh.Arm
