import VerifiedGarbage.Impl.Ecdsa.Verify.X86
import VerifiedGarbage.Impl.Ecdsa.P256.X86

/-! # ECDSA verification over P-256 on x86 (32-bit): four-word field elements and scalars -/

namespace VG.Impl.Ecdsa.Verify.X86

open VG.X86

/-- `vg_ecdsa_p256_verify`. -/
def verifyP256 : Prog isa := Cfg.verify Impl.Ecdsa.X86.p256

end VG.Impl.Ecdsa.Verify.X86
