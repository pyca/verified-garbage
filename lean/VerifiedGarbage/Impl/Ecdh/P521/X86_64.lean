import VerifiedGarbage.Impl.Ecdh.X86_64
import VerifiedGarbage.Impl.Ecdsa.P521.X86_64

/-! # ECDH over P-521 on x86-64: nine-word field elements and scalars -/

namespace VG.Impl.Ecdh.X86_64

open VG.X86_64

/-- `vg_ecdh_p521`. -/
def exchangeP521 : Prog isa := Cfg.exchange Impl.Ecdsa.X86_64.p521

end VG.Impl.Ecdh.X86_64
