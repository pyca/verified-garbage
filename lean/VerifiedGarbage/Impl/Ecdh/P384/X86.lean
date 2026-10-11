module

public import VerifiedGarbage.Impl.Ecdh.X86
public import VerifiedGarbage.Impl.Ecdsa.P384.X86

/-! # ECDH over P-384 on x86 (32-bit): six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.X86

open VG.X86

/-- `vg_ecdh_p384`. -/
def exchangeP384 : Prog isa := Cfg.exchange Impl.Ecdsa.X86.p384

end VG.Impl.Ecdh.X86
