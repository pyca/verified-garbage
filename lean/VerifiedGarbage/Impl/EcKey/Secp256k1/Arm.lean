module

public import VerifiedGarbage.Impl.EcKey.Arm
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.Arm

/-! # secp256k1 public keys on 32-bit ARM: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.EcKey.Arm

open VG.Arm

/-- `vg_ec_secp256k1_public_key`. -/
def publicKeySecp256k1 : Prog isa := Cfg.publicKey Impl.Ecdsa.Arm.secp256k1

end VG.Impl.EcKey.Arm
