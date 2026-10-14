module

public import VerifiedGarbage.Impl.Ecdsa.Verify.Arm
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.Arm

/-! # ECDSA verification over brainpoolP512r1 on 32-bit ARM: eight-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.Arm

open VG.Arm

/-- `vg_ecdsa_brainpoolp512r1_verify`. -/
def verifyBrainpoolP512r1 : Prog isa := Cfg.verify Impl.Ecdsa.Arm.brainpoolp512r1

end VG.Impl.Ecdsa.Verify.Arm
