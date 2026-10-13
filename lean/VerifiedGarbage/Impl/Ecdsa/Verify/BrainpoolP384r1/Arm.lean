module

public import VerifiedGarbage.Impl.Ecdsa.Verify.Arm
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.Arm

/-! # ECDSA verification over brainpoolP384r1 on 32-bit ARM: six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.Arm

open VG.Arm

/-- `vg_ecdsa_brainpoolp384r1_verify`. -/
def verifyBrainpoolP384r1 : Prog isa := Cfg.verify Impl.Ecdsa.Arm.brainpoolp384r1

end VG.Impl.Ecdsa.Verify.Arm
