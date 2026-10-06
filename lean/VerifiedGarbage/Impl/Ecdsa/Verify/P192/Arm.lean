import VerifiedGarbage.Impl.Ecdsa.Verify.Arm
import VerifiedGarbage.Impl.Ecdsa.P192.Arm

/-! # ECDSA verification over P-192 on 32-bit ARM: three-word field elements and scalars -/

namespace VG.Impl.Ecdsa.Verify.Arm

open VG.Arm

/-- `vg_ecdsa_p192_verify`. -/
def verifyP192 : Prog isa := Cfg.verify Impl.Ecdsa.Arm.p192

end VG.Impl.Ecdsa.Verify.Arm
