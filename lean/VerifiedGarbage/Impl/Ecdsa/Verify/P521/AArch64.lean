import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64
import VerifiedGarbage.Impl.Ecdsa.P521.AArch64

/-! # ECDSA verification over P-521 on AArch64: nine-word field elements and scalars -/

namespace VG.Impl.Ecdsa.Verify.AArch64

open VG.AArch64

/-- `vg_ecdsa_p521_verify`. -/
def verifyP521 : Prog isa := Cfg.verify Impl.Ecdsa.AArch64.p521

end VG.Impl.Ecdsa.Verify.AArch64
