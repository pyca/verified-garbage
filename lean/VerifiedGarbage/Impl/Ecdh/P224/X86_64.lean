module

public import VerifiedGarbage.Impl.Ecdh.X86_64
public import VerifiedGarbage.Impl.Ecdsa.P224.X86_64

/-! # ECDH over P-224 on x86-64: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.X86_64

open VG.X86_64

/-- `vg_ecdh_p224`. -/
def exchangeP224 : Prog isa := Cfg.exchange Impl.Ecdsa.X86_64.p224

end VG.Impl.Ecdh.X86_64
