module

public import VerifiedGarbage.Impl.Ecdh.AArch64.WindowJ
public import VerifiedGarbage.Impl.Ecdsa.P384.AArch64

/-! # ECDH over P-384 on AArch64: six-word field elements and scalars, by
windows with a Jacobian accumulator and an affine table (`Cfg.exchangeJ4`) -/

@[expose] public section

namespace VG.Impl.Ecdh.AArch64

open VG.AArch64

/-- `vg_ecdh_p384`. -/
def exchangeP384 : Prog isa := Cfg.exchangeJ4 Impl.Ecdsa.AArch64.p384

end VG.Impl.Ecdh.AArch64
