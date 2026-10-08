import VerifiedGarbage.Impl.Ecdh.X86_64
import VerifiedGarbage.Impl.Ecdsa.P521.X86_64

/-! # ECDH over P-521 on x86-64: nine-word field elements and scalars, by 4-bit
windows with a Jacobian accumulator (`Cfg.exchangeJ4`), every point of P-521
having order `n` -/

namespace VG.Impl.Ecdh.X86_64

open VG.X86_64

/-- `vg_ecdh_p521`. -/
def exchangeP521 : Prog isa := Cfg.exchangeJ4 Impl.Ecdsa.X86_64.p521

/-- `vg_ecdh_p521_adx`. -/
def exchangeP521Adx : Prog isa := Cfg.exchangeJ4 Impl.Ecdsa.X86_64.p521x

end VG.Impl.Ecdh.X86_64
