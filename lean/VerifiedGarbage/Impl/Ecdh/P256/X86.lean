import VerifiedGarbage.Impl.Ecdh.X86
import VerifiedGarbage.Impl.Ecdsa.P256.X86

/-! # ECDH over P-256 on x86 (32-bit): four-word field elements and scalars -/

namespace VG.Impl.Ecdh.X86

open VG.X86

/-- `vg_ecdh_p256`. -/
def exchangeP256 : Prog isa := Cfg.exchange Impl.Ecdsa.X86.p256

end VG.Impl.Ecdh.X86
