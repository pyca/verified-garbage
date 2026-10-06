import VerifiedGarbage.Impl.Ecdsa.Verify.X86
import VerifiedGarbage.Impl.Ecdsa.P224.X86

/-! # ECDSA verification over P-224 on x86 (32-bit): four-word field elements and scalars -/

namespace VG.Impl.Ecdsa.Verify.X86

open VG.X86

/-- `vg_ecdsa_p224_verify`. -/
def verifyP224 : Prog isa := Cfg.verify Impl.Ecdsa.X86.p224

end VG.Impl.Ecdsa.Verify.X86
