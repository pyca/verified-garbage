module

public import VerifiedGarbage.Impl.Ecdh.X86
public import VerifiedGarbage.Impl.Ecdsa.P384.X86
public import VerifiedGarbage.Impl.Scrub.X86

/-! # ECDH over P-384 on x86 (32-bit): six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.X86

open VG.X86

/-- `vg_ecdh_p384`. -/
def exchangeP384 : Prog isa := Cfg.exchange Impl.Ecdsa.X86.p384

end VG.Impl.Ecdh.X86

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubAll rb W`): the `W`
bytes of stack below `esp` that its frames and calls use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue. -/

namespace VG.Impl.Ecdh.X86.Fn

open VG.X86

/-- `vg_ecdh_p384`, as emitted. -/
def exchangeP384 : Prog isa := Impl.Scrub.X86.scrubAll 32 28 Impl.Ecdh.X86.exchangeP384

end VG.Impl.Ecdh.X86.Fn
