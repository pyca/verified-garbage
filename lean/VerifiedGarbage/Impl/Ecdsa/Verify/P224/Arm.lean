import VerifiedGarbage.Impl.Ecdsa.Verify.Arm
import VerifiedGarbage.Impl.Ecdsa.P224.Arm

/-! # ECDSA verification over P-224 on 32-bit ARM: four-word field elements and scalars -/

namespace VG.Impl.Ecdsa.Verify.Arm

open VG.Arm

/-- `vg_ecdsa_p224_verify`. -/
def verifyP224 : Prog isa := Cfg.verify Impl.Ecdsa.Arm.p224

end VG.Impl.Ecdsa.Verify.Arm
