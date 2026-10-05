import VerifiedGarbage.Impl.Ecdsa.Verify.X86_64
import VerifiedGarbage.Impl.Ecdsa.P384.X86_64

/-! # ECDSA verification over P-384 on x86-64: six-word field elements and scalars -/

namespace VG.Impl.Ecdsa.Verify.X86_64

open VG.X86_64

/-- `vg_ecdsa_p384_verify`. -/
def verifyP384 : Prog isa := Cfg.verify Impl.Ecdsa.X86_64.p384

end VG.Impl.Ecdsa.Verify.X86_64
