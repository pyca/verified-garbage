module

public import VerifiedGarbage.Impl.Ecdh.AArch64
public import VerifiedGarbage.Impl.Ecdsa.P521.AArch64

/-! # ECDH over P-521 on AArch64: nine-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.AArch64

open VG.AArch64

/-- `vg_ecdh_p521`. -/
def exchangeP521 : Prog isa := Cfg.exchange Impl.Ecdsa.AArch64.p521

end VG.Impl.Ecdh.AArch64
