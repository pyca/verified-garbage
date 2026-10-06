import VerifiedGarbage.Impl.Ecdh.X86
import VerifiedGarbage.Impl.Ecdsa.P224.X86

/-! # ECDH over P-224 on x86 (32-bit): four-word field elements and scalars -/

namespace VG.Impl.Ecdh.X86

open VG.X86

/-- `vg_ecdh_p224`. -/
def exchangeP224 : Prog isa := Cfg.exchange Impl.Ecdsa.X86.p224

end VG.Impl.Ecdh.X86
