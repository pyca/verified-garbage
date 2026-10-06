import VerifiedGarbage.Impl.Ecdh.Arm
import VerifiedGarbage.Impl.Ecdsa.P224.Arm

/-! # ECDH over P-224 on 32-bit ARM: four-word field elements and scalars -/

namespace VG.Impl.Ecdh.Arm

open VG.Arm

/-- `vg_ecdh_p224`. -/
def exchangeP224 : Prog isa := Cfg.exchange Impl.Ecdsa.Arm.p224

end VG.Impl.Ecdh.Arm
