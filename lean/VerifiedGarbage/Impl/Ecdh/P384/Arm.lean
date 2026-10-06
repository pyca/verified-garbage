import VerifiedGarbage.Impl.Ecdh.Arm
import VerifiedGarbage.Impl.Ecdsa.P384.Arm

/-! # ECDH over P-384 on 32-bit ARM: six-word field elements and scalars -/

namespace VG.Impl.Ecdh.Arm

open VG.Arm

/-- `vg_ecdh_p384`. -/
def exchangeP384 : Prog isa := Cfg.exchange Impl.Ecdsa.Arm.p384

end VG.Impl.Ecdh.Arm
