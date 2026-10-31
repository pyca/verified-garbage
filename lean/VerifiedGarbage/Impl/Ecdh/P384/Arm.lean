module

public import VerifiedGarbage.Impl.Ecdh.Arm
public import VerifiedGarbage.Impl.Ecdsa.P384.Arm

/-! # ECDH over P-384 on 32-bit ARM: six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.Arm

open VG.Arm

/-- `vg_ecdh_p384`, or with `u` `vg_ecdh_p384_umaal`. -/
def exchangeP384With (u : Bool) : Prog isa := Cfg.exchange (Impl.Ecdsa.Arm.p384With u)

/-- `vg_ecdh_p384`. -/
def exchangeP384 : Prog isa := exchangeP384With false

/-- `vg_ecdh_p384_umaal`. -/
def exchangeP384U : Prog isa := exchangeP384With true

end VG.Impl.Ecdh.Arm
