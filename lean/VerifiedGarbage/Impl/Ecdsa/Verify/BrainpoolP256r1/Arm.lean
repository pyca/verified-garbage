module

public import VerifiedGarbage.Impl.Ecdsa.Verify.Arm
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP256r1.Arm

/-! # ECDSA verification over brainpoolP256r1 on 32-bit ARM: four-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.Arm

open VG.Arm

/-- `vg_ecdsa_brainpoolp256r1_verify`. -/
def verifyBrainpoolP256r1 : Prog isa := Cfg.verify Impl.Ecdsa.Arm.brainpoolp256r1

end VG.Impl.Ecdsa.Verify.Arm
