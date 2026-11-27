module

public import VerifiedGarbage.Impl.Ecdh.X86
public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.X86
public import VerifiedGarbage.Impl.Scrub.X86

/-! # ECDH over secp256k1 on x86 (32-bit): four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.X86

open VG.X86

/-- `vg_ecdh_secp256k1`. -/
def exchangeSecp256k1 : Prog isa := Cfg.exchange Impl.Ecdsa.X86.secp256k1

end VG.Impl.Ecdh.X86

/-! ## The functions as emitted

Each function, then its cleanup (`Impl.Scrub.X86.scrubAll rb W`): the `W`
bytes of stack below `esp` that its frames and calls use zeroed, and the
registers a callee may change cleared but the `rb` bits of the result, so
that it returns without secret residue. -/

namespace VG.Impl.Ecdh.X86.Fn

open VG.X86

/-- `vg_ecdh_secp256k1`, as emitted. -/
def exchangeSecp256k1 : Prog isa := Impl.Scrub.X86.scrubAll 32 28 Impl.Ecdh.X86.exchangeSecp256k1

end VG.Impl.Ecdh.X86.Fn
