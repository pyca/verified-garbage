module

public import VerifiedGarbage.Impl.Ecdh.X86_64
public import VerifiedGarbage.Impl.Ecdsa.P256.X86_64
public import VerifiedGarbage.Impl.P256.X86_64.DoubleHalfPublic

/-! # ECDH over P-256 on x86-64: four-word field elements and scalars, by the
Jacobian window method (`Cfg.exchangeJ`, P-256 having prime order) with the
doubling by halving (`Impl/P256/X86_64/DoubleHalfPublic.lean`) -/

@[expose] public section

namespace VG.Impl.Ecdh.X86_64

open VG.X86_64

/-- `vg_ecdh_p256`. -/
def exchangeP256 : Prog isa :=
  Cfg.exchangeJ Impl.Ecdsa.X86_64.p256
    (Impl.P256.X86_64.doubleHalfPublic Impl.Ecdsa.X86_64.p256.MP' Impl.Ecdsa.X86_64.p256.rcbSlots)

/-- `vg_ecdh_p256_adx`. -/
def exchangeP256Adx : Prog isa :=
  Cfg.exchangeJ Impl.Ecdsa.X86_64.p256x
    (Impl.P256.X86_64.doubleHalfPublic Impl.Ecdsa.X86_64.p256x.MP' Impl.Ecdsa.X86_64.p256x.rcbSlots)

end VG.Impl.Ecdh.X86_64
