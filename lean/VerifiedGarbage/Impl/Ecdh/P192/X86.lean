module

public import VerifiedGarbage.Impl.Ecdh.X86
public import VerifiedGarbage.Impl.Ecdsa.P192.X86

/-! # ECDH over P-192 on x86 (32-bit): three-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.X86

open VG.X86

/-- `vg_ecdh_p192`. -/
def exchangeP192 : Prog isa := Cfg.exchange Impl.Ecdsa.X86.p192

end VG.Impl.Ecdh.X86
