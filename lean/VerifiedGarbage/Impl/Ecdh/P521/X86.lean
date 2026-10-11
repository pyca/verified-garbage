module

public import VerifiedGarbage.Impl.Ecdh.X86
public import VerifiedGarbage.Impl.Ecdsa.P521.X86

/-! # ECDH over P-521 on x86 (32-bit): nine-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.X86

open VG.X86

/-- `vg_ecdh_p521`. -/
def exchangeP521 : Prog isa := Cfg.exchange Impl.Ecdsa.X86.p521

end VG.Impl.Ecdh.X86
