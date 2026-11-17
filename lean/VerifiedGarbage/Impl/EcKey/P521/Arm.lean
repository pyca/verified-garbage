module

public import VerifiedGarbage.Impl.EcKey.Arm
public import VerifiedGarbage.Impl.Ecdsa.P521.Arm

/-! # P-521 public keys on 32-bit ARM: nine-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.Arm

open VG.Arm

/-- `vg_ec_p521_public_key`, or with `u` `vg_ec_p521_public_key_umaal`. -/
def publicKeyP521With (u : Bool) : Prog isa := Cfg.publicKey (Impl.Ecdsa.Arm.p521With u)

/-- `vg_ec_p521_public_key`. -/
def publicKeyP521 : Prog isa := publicKeyP521With false

/-- `vg_ec_p521_public_key_umaal`. -/
def publicKeyP521U : Prog isa := publicKeyP521With true

end VG.Impl.EcKey.Arm
