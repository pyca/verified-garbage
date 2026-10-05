import VerifiedGarbage.Impl.Ecdsa.Verify.X86
import VerifiedGarbage.Impl.Ecdsa.P521.X86

/-! # ECDSA verification over P-521 on x86 (32-bit): nine-word field elements and scalars -/

namespace VG.Impl.Ecdsa.Verify.X86

open VG.X86

/-- `vg_ecdsa_p521_verify`. -/
def verifyP521 : Prog isa := Cfg.verify Impl.Ecdsa.X86.p521

end VG.Impl.Ecdsa.Verify.X86
