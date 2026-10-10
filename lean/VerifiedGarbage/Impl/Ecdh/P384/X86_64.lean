import VerifiedGarbage.Impl.Ecdh.X86_64
import VerifiedGarbage.Impl.Ecdsa.P384.X86_64
import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleIn
import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleCms

/-! # ECDH over P-384 on x86-64: six-word field elements and scalars, by the
Jacobian window method with an affine table (`Cfg.exchangeJA`, P-384 having
prime order) with the doubling in place
(`Impl/Weierstrass/X86_64/DoubleIn.lean`; with BMI2 and ADX, with its small
multiples fused, `Impl/Weierstrass/X86_64/DoubleCms.lean`) -/

namespace VG.Impl.Ecdh.X86_64

open VG.X86_64

/-- `vg_ecdh_p384`. -/
def exchangeP384 : Prog isa :=
  Cfg.exchangeJA Impl.Ecdsa.X86_64.p384
    (Impl.Weierstrass.X86_64.doubleIn Impl.Ecdsa.X86_64.p384.MH Impl.Ecdsa.X86_64.p384.rcbSlots)

/-- `vg_ecdh_p384_adx`. -/
def exchangeP384Adx : Prog isa :=
  Cfg.exchangeJA Impl.Ecdsa.X86_64.p384x
    (Impl.Weierstrass.X86_64.doubleCms Impl.Ecdsa.X86_64.p384x.MP' Impl.Ecdsa.X86_64.p384x.rcbSlots)

end VG.Impl.Ecdh.X86_64
