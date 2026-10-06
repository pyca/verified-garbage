import VerifiedGarbage.Impl.Ecdsa.Verify.X86
import VerifiedGarbage.Impl.Ecdsa.P384.X86

/-! # ECDSA verification over P-384 on x86 (32-bit): six-word field elements and scalars -/

namespace VG.Impl.Ecdsa.Verify.X86

open VG.X86

/-- `vg_ecdsa_p384_verify`. -/
def verifyP384 : Prog isa := Cfg.verify Impl.Ecdsa.X86.p384

end VG.Impl.Ecdsa.Verify.X86
