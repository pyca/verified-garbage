module

public import VerifiedGarbage.Impl.Ecdh.AArch64
public import VerifiedGarbage.Impl.Ecdsa.P256.AArch64

/-! # ECDH over P-256 on AArch64: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.AArch64

open VG.AArch64

/-- `vg_ecdh_p256`. -/
def exchangeP256 : Prog isa := Cfg.exchange Impl.Ecdsa.AArch64.p256

end VG.Impl.Ecdh.AArch64
