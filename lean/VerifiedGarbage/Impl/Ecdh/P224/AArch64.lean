import VerifiedGarbage.Impl.Ecdh.AArch64
import VerifiedGarbage.Impl.Ecdsa.P224.AArch64

/-! # ECDH over P-224 on AArch64: four-word field elements and scalars -/

namespace VG.Impl.Ecdh.AArch64

open VG.AArch64

/-- `vg_ecdh_p224`. -/
def exchangeP224 : Prog isa := Cfg.exchange Impl.Ecdsa.AArch64.p224

end VG.Impl.Ecdh.AArch64
