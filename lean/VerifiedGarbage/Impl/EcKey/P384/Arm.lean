import VerifiedGarbage.Impl.EcKey.Arm
import VerifiedGarbage.Impl.Ecdsa.P384.Arm

/-! # P-384 public keys on 32-bit ARM: six-word field elements and scalars -/

namespace VG.Impl.EcKey.Arm

open VG.Arm

/-- `vg_ec_p384_public_key`. -/
def publicKeyP384 : Prog isa := Cfg.publicKey Impl.Ecdsa.Arm.p384

end VG.Impl.EcKey.Arm
