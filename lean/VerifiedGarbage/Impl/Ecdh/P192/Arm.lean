module

public import VerifiedGarbage.Impl.Ecdh.Arm
public import VerifiedGarbage.Impl.Ecdsa.P192.Arm

/-! # ECDH over P-192 on 32-bit ARM: three-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.Arm

open VG.Arm

/-- `vg_ecdh_p192`. -/
def exchangeP192 : Prog isa := Cfg.exchange Impl.Ecdsa.Arm.p192

end VG.Impl.Ecdh.Arm
