import VerifiedGarbage.Impl.Ecdsa.Verify.Arm
import VerifiedGarbage.Impl.Ecdsa.P384.Arm

/-! # ECDSA verification over P-384 on 32-bit ARM: six-word field elements and scalars -/

namespace VG.Impl.Ecdsa.Verify.Arm

open VG.Arm

/-- `vg_ecdsa_p384_verify`. -/
def verifyP384 : Prog isa := Cfg.verify Impl.Ecdsa.Arm.p384

end VG.Impl.Ecdsa.Verify.Arm
