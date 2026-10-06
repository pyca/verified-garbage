import VerifiedGarbage.Impl.Ecdsa.Verify.X86
import VerifiedGarbage.Impl.Ecdsa.P192.X86

/-! # ECDSA verification over P-192 on x86 (32-bit): three-word field elements and scalars -/

namespace VG.Impl.Ecdsa.Verify.X86

open VG.X86

/-- `vg_ecdsa_p192_verify`. -/
def verifyP192 : Prog isa := Cfg.verify Impl.Ecdsa.X86.p192

end VG.Impl.Ecdsa.Verify.X86
