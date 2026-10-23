module

public import VerifiedGarbage.Impl.Ecdh.PPC64LE
public import VerifiedGarbage.Impl.Ecdsa.P224.PPC64LE

/-! # ECDH over P-224 on PPC64LE: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.PPC64LE

open VG.PPC64LE

/-- `vg_ecdh_p224`. -/
def exchangeP224 : Prog isa := Cfg.exchange Impl.Ecdsa.PPC64LE.p224

end VG.Impl.Ecdh.PPC64LE
