import VerifiedGarbage.Impl.Ecdh.X86_64
import VerifiedGarbage.Impl.Ecdsa.P384.X86_64

/-! # ECDH over P-384 on x86-64: six-word field elements and scalars -/

namespace VG.Impl.Ecdh.X86_64

open VG.X86_64

/-- `vg_ecdh_p384`. -/
def exchangeP384 : Prog isa := Cfg.exchange Impl.Ecdsa.X86_64.p384

/-- `vg_ecdh_p384_adx`. -/
def exchangeP384Adx : Prog isa := Cfg.exchange Impl.Ecdsa.X86_64.p384x

end VG.Impl.Ecdh.X86_64
