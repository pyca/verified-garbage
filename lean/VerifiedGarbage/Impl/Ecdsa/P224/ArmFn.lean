module

public import VerifiedGarbage.Impl.Ecdsa.P224.ArmComb
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.Impl.Residue.Arm
public import VerifiedGarbage.Spec.Ecdsa.Verify.P224

/-!
# ECDSA over P-224 on 32-bit ARM, as emitted

`vg_ecdsa_p224_verify` and its `_umaal` variant: each one's code, which keeps
the hash's working values in a frame of 96 bytes, then the instructions that
zero those bytes and set the registers a callee may change, but the result,
and the flags to constants (`Impl.Residue.Arm.scrubF`).
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_ecdsa_p224_verify`. -/
def verifyP224 : Prog isa :=
  scrubF 32 96
    (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P224.inst.curve.len false Impl.Ecdsa.Arm.verifyP224Comb)

/-- `vg_ecdsa_p224_verify_umaal`. -/
def verifyP224U : Prog isa :=
  scrubF 32 96
    (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P224.inst.curve.len false Impl.Ecdsa.Arm.verifyP224CombU)

end VG.Impl.Ecdsa.Arm.Fn
