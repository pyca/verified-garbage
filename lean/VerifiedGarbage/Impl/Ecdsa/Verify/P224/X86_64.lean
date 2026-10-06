import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64
import VerifiedGarbage.Impl.Ecdsa.P224.X86_64

/-! # ECDSA verification over P-224 on x86-64: four-word field elements and scalars -/

namespace VG.Impl.Ecdsa.Verify.X86_64

open VG.X86_64

/-- `vg_ecdsa_p224_verify`. -/
def verifyP224 : Prog isa := Cfg.verify Impl.Ecdsa.X86_64.p224

end VG.Impl.Ecdsa.Verify.X86_64
