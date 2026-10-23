module

public import VerifiedGarbage.Impl.Ecdh.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P384.PPC64LE

/-! # ECDH over P-384 on PPC64LE: six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.PPC64LE

open VG.PPC64LE

/-- `vg_ecdh_p384`. -/
def exchangeP384 : Prog isa := Cfg.exchange Impl.Ecdsa.PPC64LE.p384

end VG.Impl.Ecdh.PPC64LE
