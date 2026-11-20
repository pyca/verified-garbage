module

public import VerifiedGarbage.Impl.Ecdh.X86
public import VerifiedGarbage.Impl.Ecdsa.P192.X86
public import VerifiedGarbage.Impl.Scrub.X86

/-! # ECDH over P-192 on x86 (32-bit): three-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.X86

open VG.X86

/-- `vg_ecdh_p192`. -/
def exchangeP192 : Prog isa := Cfg.exchange Impl.Ecdsa.X86.p192

end VG.Impl.Ecdh.X86

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubF rb W`): the `W`
bytes of stack below `esp` that its frames and calls use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue. -/

namespace VG.Impl.Ecdh.X86.Fn

open VG.X86

/-- `vg_ecdh_p192`, as emitted. -/
def exchangeP192 : Prog isa := Impl.Scrub.X86.scrubF 32 28 Impl.Ecdh.X86.exchangeP192

end VG.Impl.Ecdh.X86.Fn
