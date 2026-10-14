module

public import VerifiedGarbage.Impl.Ecdh.Arm
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.Arm

/-! # ECDH over secp256k1 on 32-bit ARM: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.Arm

open VG.Arm

/-- `vg_ecdh_secp256k1`. -/
def exchangeSecp256k1 : Prog isa := Cfg.exchange Impl.Ecdsa.Arm.secp256k1

end VG.Impl.Ecdh.Arm
