module

public import VerifiedGarbage.Impl.Ecdh.X86_64
public import VerifiedGarbage.Impl.Ecdsa.P521.X86_64
public import VerifiedGarbage.Impl.Weierstrass.X86_64.P521Win

/-! # ECDH over P-521 on x86-64: nine-word field elements and scalars, by 4-bit
windows with a Jacobian accumulator (`Cfg.exchangeJ4`), every point of P-521
having order `n` -/

@[expose] public section

namespace VG.Impl.Ecdh.X86_64

open VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass VG.Impl.Ecdsa.X86_64

/-- `vg_ecdh_p521`. -/
def exchangeP521 : Prog isa := Cfg.exchangeJ4 Impl.Ecdsa.X86_64.p521

/-- `Cfg.mulQJ4` by the fast steps (`P521Win.lean`): `[d]P` into `R` by 4-bit
windows, the doublings in place and the mixed additions by calls of
`vg_p521_sqr_adx`, `vg_p521_mul_adx` and `vg_p521_mulw_adx`. -/
def Cfg.mulQJ4F (c : Impl.Ecdsa.X86_64.Cfg) : Prog isa :=
  .seq (.block (maskK c))
    (.seq (c.winPrep (c.sl K)) (Impl.Weierstrass.X86_64.P521F.Win.windowF (c.winCfg PX PY BP)
      (InvCfg.inv (Cfg.invWin c))))

/-- `vg_ecdh_p521_adx`. -/
def exchangeP521Adx : Prog isa := Cfg.exchangeWith Impl.Ecdsa.X86_64.p521x (Cfg.mulQJ4F Impl.Ecdsa.X86_64.p521x)

end VG.Impl.Ecdh.X86_64
