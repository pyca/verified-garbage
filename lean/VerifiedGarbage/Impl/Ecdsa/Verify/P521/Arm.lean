module

public import VerifiedGarbage.Impl.Ecdsa.Verify.Arm
public import VerifiedGarbage.Impl.Ecdsa.P521.Arm

/-! # ECDSA verification over P-521 on 32-bit ARM: nine-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.Arm

open VG.Arm

/-- `vg_ecdsa_p521_verify`. -/
def verifyP521 : Prog isa := Cfg.verify Impl.Ecdsa.Arm.p521

end VG.Impl.Ecdsa.Verify.Arm
