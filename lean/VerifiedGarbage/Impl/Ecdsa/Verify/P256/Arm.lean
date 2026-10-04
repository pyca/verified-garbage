import VerifiedGarbage.Impl.Ecdsa.Verify.Arm
import VerifiedGarbage.Impl.Ecdsa.P256.Arm

/-! # ECDSA verification over P-256 on 32-bit ARM: four-word field elements and scalars -/

namespace VG.Impl.Ecdsa.Verify.Arm

open VG.Arm

/-- `vg_ecdsa_p256_verify`. -/
def verifyP256 : Prog isa := Cfg.verify Impl.Ecdsa.Arm.p256

end VG.Impl.Ecdsa.Verify.Arm
