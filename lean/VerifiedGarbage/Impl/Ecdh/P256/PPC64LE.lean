module

public import VerifiedGarbage.Impl.Ecdh.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P256.PPC64LE

/-! # ECDH over P-256 on PPC64LE: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.PPC64LE

open VG.PPC64LE

/-- `vg_ecdh_p256`. -/
def exchangeP256 : Prog isa := Cfg.exchange Impl.Ecdsa.PPC64LE.p256

end VG.Impl.Ecdh.PPC64LE
