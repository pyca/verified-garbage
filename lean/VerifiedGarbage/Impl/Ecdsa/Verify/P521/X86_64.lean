import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64
import VerifiedGarbage.Impl.Ecdsa.P521.X86_64

/-! # ECDSA verification over P-521 on x86-64: nine-word field elements and scalars -/

namespace VG.Impl.Ecdsa.Verify.X86_64

open VG.X86_64

/-- `vg_ecdsa_p521_verify`. -/
def verifyP521 : Prog isa := Cfg.verify Impl.Ecdsa.X86_64.p521

/-- `vg_ecdsa_p521_verify_adx`. -/
def verifyP521Adx : Prog isa := Cfg.verify Impl.Ecdsa.X86_64.p521x

end VG.Impl.Ecdsa.Verify.X86_64
