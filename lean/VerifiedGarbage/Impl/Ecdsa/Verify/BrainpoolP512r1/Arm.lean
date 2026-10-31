module

public import VerifiedGarbage.Impl.Ecdsa.Verify.Arm
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.Arm

/-! # ECDSA verification over brainpoolP512r1 on 32-bit ARM: eight-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.Arm

open VG.Arm

/-- `vg_ecdsa_brainpoolp512r1_verify`, or with `u` `vg_ecdsa_brainpoolp512r1_verify_umaal`. -/
def verifyBrainpoolP512r1With (u : Bool) : Prog isa := Cfg.verify (Impl.Ecdsa.Arm.brainpoolp512r1With u)

/-- `vg_ecdsa_brainpoolp512r1_verify`. -/
def verifyBrainpoolP512r1 : Prog isa := verifyBrainpoolP512r1With false

/-- `vg_ecdsa_brainpoolp512r1_verify_umaal`. -/
def verifyBrainpoolP512r1U : Prog isa := verifyBrainpoolP512r1With true

end VG.Impl.Ecdsa.Verify.Arm
