module

public import VerifiedGarbage.Impl.Ecdh.Arm
public import VerifiedGarbage.Impl.Ecdsa.P256.Arm

/-! # ECDH over P-256 on 32-bit ARM: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.Arm

open VG.Arm

/-- `vg_ecdh_p256`, or with `u` `vg_ecdh_p256_umaal`. -/
def exchangeP256With (u : Bool) : Prog isa := Cfg.exchange (Impl.Ecdsa.Arm.p256With u)

/-- `vg_ecdh_p256`. -/
def exchangeP256 : Prog isa := exchangeP256With false

/-- `vg_ecdh_p256_umaal`. -/
def exchangeP256U : Prog isa := exchangeP256With true

end VG.Impl.Ecdh.Arm
