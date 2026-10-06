import VerifiedGarbage.Impl.EcKey.Arm
import VerifiedGarbage.Impl.Ecdsa.P192.Arm

/-! # P-192 public keys on 32-bit ARM: three-word field elements and scalars -/

namespace VG.Impl.EcKey.Arm

open VG.Arm

/-- `vg_ec_p192_public_key`. -/
def publicKeyP192 : Prog isa := Cfg.publicKey Impl.Ecdsa.Arm.p192

end VG.Impl.EcKey.Arm
