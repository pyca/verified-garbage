module

public import VerifiedGarbage.Impl.Scrub.X86_64.Fn
public import VerifiedGarbage.Impl.Ecdh.X86_64
public import VerifiedGarbage.Impl.Ecdsa.P256.X86_64
public import VerifiedGarbage.Impl.P256.X86_64.DoubleHalfPublic

/-! # ECDH over P-256 on x86-64: four-word field elements and scalars, by odd
5-bit windows in Jacobian coordinates, each window's selection woven into
the addition before it (`Cfg.exchangeJO`, P-256 having prime
order `n` with `n mod 64 = 17`) with the doubling by halving
(`Impl/P256/X86_64/DoubleHalfPublic.lean`) -/

@[expose] public section

namespace VG.Impl.Ecdh.X86_64

open VG.X86_64

/-- `vg_ecdh_p256`. -/
def exchangeP256 : Prog isa :=
  Cfg.exchangeJO Impl.Ecdsa.X86_64.p256
    (Impl.P256.X86_64.doubleHalfPublic Impl.Ecdsa.X86_64.p256.MP' Impl.Ecdsa.X86_64.p256.rcbSlots)

/-- `vg_ecdh_p256_adx`. -/
def exchangeP256Adx : Prog isa :=
  Cfg.exchangeJO Impl.Ecdsa.X86_64.p256x
    (Impl.P256.X86_64.doubleHalfPublic Impl.Ecdsa.X86_64.p256x.MP' Impl.Ecdsa.X86_64.p256x.rcbSlots)

end VG.Impl.Ecdh.X86_64

namespace VG.Impl.Ecdh.X86_64.Fn

open VG.X86_64
open VG.Impl.Scrub.X86_64 (scrubAll)

/-- `vg_ecdh_p256` as emitted: its code, then its cleanup. -/
def exchangeP256 : Prog isa := scrubAll .sse 32 8 _root_.VG.Impl.Ecdh.X86_64.exchangeP256

/-- `vg_ecdh_p256_adx` as emitted: its code, then its cleanup. -/
def exchangeP256Adx : Prog isa := scrubAll .avx 32 8 _root_.VG.Impl.Ecdh.X86_64.exchangeP256Adx

end VG.Impl.Ecdh.X86_64.Fn
