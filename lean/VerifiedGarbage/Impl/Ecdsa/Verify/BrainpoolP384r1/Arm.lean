module

public import VerifiedGarbage.Impl.Ecdsa.Verify.Arm
public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.Arm

/-! # ECDSA verification over brainpoolP384r1 on 32-bit ARM: six-word field elements and scalars -/

@[expose] public section

namespace VG.Impl.Ecdsa.Verify.Arm

open VG.Arm

/-- `vg_ecdsa_brainpoolp384r1_verify`, or with `u` `vg_ecdsa_brainpoolp384r1_verify_umaal`. -/
def verifyBrainpoolP384r1With (u : Bool) : Prog isa := Cfg.verify (Impl.Ecdsa.Arm.brainpoolp384r1With u)

/-- `vg_ecdsa_brainpoolp384r1_verify`. -/
def verifyBrainpoolP384r1 : Prog isa := verifyBrainpoolP384r1With false

/-- `vg_ecdsa_brainpoolp384r1_verify_umaal`. -/
def verifyBrainpoolP384r1U : Prog isa := verifyBrainpoolP384r1With true

end VG.Impl.Ecdsa.Verify.Arm
