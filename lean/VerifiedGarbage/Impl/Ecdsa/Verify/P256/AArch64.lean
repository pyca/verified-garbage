import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64
import VerifiedGarbage.Impl.Ecdsa.P256.AArch64

/-! # ECDSA verification over P-256 on AArch64: four-word field elements and scalars -/

namespace VG.Impl.Ecdsa.Verify.AArch64

open VG.AArch64

/-- `vg_ecdsa_p256_verify`. -/
def verifyP256 : Prog isa := Cfg.verify Impl.Ecdsa.AArch64.p256

end VG.Impl.Ecdsa.Verify.AArch64
