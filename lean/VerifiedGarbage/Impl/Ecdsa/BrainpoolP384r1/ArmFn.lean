module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP384r1.ArmComb
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.Impl.Residue.Arm
public import VerifiedGarbage.Spec.Ecdsa.Verify.BrainpoolP384r1

/-!
# ECDSA over brainpoolP384r1 on 32-bit ARM, as emitted

`vg_ecdsa_brainpoolp384r1_verify` and its `_umaal` variant: each one's code, which keeps
the hash's working values in a frame of 96 bytes, then the instructions that
zero those bytes and set the registers a callee may change, but the result,
and the flags to constants (`Impl.Residue.Arm.scrubF`).
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_ecdsa_brainpoolp384r1_verify`. -/
def verifyBrainpoolP384r1 : Prog isa :=
  scrubF 32 96
    (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP384r1.inst.curve.len false Impl.Ecdsa.Arm.verifyBrainpoolP384r1Comb)

/-- `vg_ecdsa_brainpoolp384r1_verify_umaal`. -/
def verifyBrainpoolP384r1U : Prog isa :=
  scrubF 32 96
    (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.BrainpoolP384r1.inst.curve.len false Impl.Ecdsa.Arm.verifyBrainpoolP384r1CombU)

end VG.Impl.Ecdsa.Arm.Fn
