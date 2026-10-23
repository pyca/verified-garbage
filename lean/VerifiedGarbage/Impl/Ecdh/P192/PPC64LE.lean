module

public import VerifiedGarbage.Impl.Ecdh.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P192.PPC64LE

/-! # ECDH over P-192 on PPC64LE: three-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.PPC64LE

open VG.PPC64LE

/-- `vg_ecdh_p192`. -/
def exchangeP192 : Prog isa := Cfg.exchange Impl.Ecdsa.PPC64LE.p192

end VG.Impl.Ecdh.PPC64LE
