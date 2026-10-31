module

public import VerifiedGarbage.Impl.Ecdh.Arm
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.Arm

/-! # ECDH over secp256k1 on 32-bit ARM: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.Arm

open VG.Arm

/-- `vg_ecdh_secp256k1`, or with `u` `vg_ecdh_secp256k1_umaal`. -/
def exchangeSecp256k1With (u : Bool) : Prog isa := Cfg.exchange (Impl.Ecdsa.Arm.secp256k1With u)

/-- `vg_ecdh_secp256k1`. -/
def exchangeSecp256k1 : Prog isa := exchangeSecp256k1With false

/-- `vg_ecdh_secp256k1_umaal`. -/
def exchangeSecp256k1U : Prog isa := exchangeSecp256k1With true

end VG.Impl.Ecdh.Arm
