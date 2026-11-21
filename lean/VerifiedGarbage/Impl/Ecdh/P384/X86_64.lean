module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.Ecdh.X86_64
public import VerifiedGarbage.Impl.Ecdsa.P384.X86_64
public import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleIn
public import VerifiedGarbage.Impl.Weierstrass.X86_64.DoubleCms

/-! # ECDH over P-384 on x86-64: six-word field elements and scalars, by the
Jacobian window method with an affine table (`Cfg.exchangeJA`, P-384 having
prime order) with the doubling in place
(`Impl/Weierstrass/X86_64/DoubleIn.lean`; with BMI2 and ADX, with its small
multiples fused, `Impl/Weierstrass/X86_64/DoubleCms.lean`) -/

@[expose] public section

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

namespace VG.Impl.Ecdh.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubAll)

/-- `vg_ecdh_p384` as emitted: its code, then its cleanup. -/
def exchangeP384 : Prog isa := scrubAll .sse 32 8 _root_.VG.Impl.Ecdh.X86_64.exchangeP384

/-- `vg_ecdh_p384_adx` as emitted: its code, then its cleanup. -/
def exchangeP384Adx : Prog isa := scrubAll .avx 32 8 _root_.VG.Impl.Ecdh.X86_64.exchangeP384Adx

end VG.Impl.Ecdh.X86_64.Fn
