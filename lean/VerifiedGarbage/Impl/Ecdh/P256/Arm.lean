module

public import VerifiedGarbage.Impl.Ecdh.Arm
public import VerifiedGarbage.Impl.Ecdsa.P256.Arm

/-! # ECDH over P-256 on 32-bit ARM: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdh.Arm

open VG.Arm

/-- `vg_ecdh_p256`. -/
def exchangeP256 : Prog isa := Cfg.exchange Impl.Ecdsa.Arm.p256

end VG.Impl.Ecdh.Arm
