import VerifiedGarbage.Impl.EcKey.Arm
import VerifiedGarbage.Impl.Ecdsa.P521.Arm

/-! # P-521 public keys on 32-bit ARM: nine-word field elements and scalars -/

namespace VG.Impl.EcKey.Arm

open VG.Arm

/-- `vg_ec_p521_public_key`. -/
def publicKeyP521 : Prog isa := Cfg.publicKey Impl.Ecdsa.Arm.p521

end VG.Impl.EcKey.Arm
