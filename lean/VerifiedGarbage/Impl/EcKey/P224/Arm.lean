module

public import VerifiedGarbage.Impl.EcKey.Arm
public import VerifiedGarbage.Impl.Ecdsa.P224.Arm

/-! # P-224 public keys on 32-bit ARM: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.Arm

open VG.Arm

/-- `vg_ec_p224_public_key`. -/
def publicKeyP224 : Prog isa := Cfg.publicKey Impl.Ecdsa.Arm.p224

end VG.Impl.EcKey.Arm
