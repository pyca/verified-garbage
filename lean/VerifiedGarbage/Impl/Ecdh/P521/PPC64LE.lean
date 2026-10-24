module

public import VerifiedGarbage.Impl.Ecdh.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P521.PPC64LE

/-! # ECDH over P-521 on PPC64LE: nine-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.PPC64LE

open VG.PPC64LE

/-- `vg_ecdh_p521`. -/
def exchangeP521 : Prog isa := Cfg.exchange Impl.Ecdsa.PPC64LE.p521

end VG.Impl.Ecdh.PPC64LE
