module

public import VerifiedGarbage.Impl.Ecdsa.P192.ArmComb
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.Impl.Residue.Arm
public import VerifiedGarbage.Spec.Ecdsa.Verify.P192

/-!
# ECDSA over P-192 on 32-bit ARM, as emitted

`vg_ecdsa_p192_verify` and its `_umaal` variant: each one's code, which keeps
the hash's working values in a frame of 96 bytes, then the instructions that
zero those bytes and set the registers a callee may change, but the result,
and the flags to constants (`Impl.Residue.Arm.scrubF`).
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_ecdsa_p192_verify`. -/
def verifyP192 : Prog isa :=
  scrubF 32 96
    (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P192.inst.curve.len false Impl.Ecdsa.Arm.verifyP192Comb)

/-- `vg_ecdsa_p192_verify_umaal`. -/
def verifyP192U : Prog isa :=
  scrubF 32 96
    (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P192.inst.curve.len false Impl.Ecdsa.Arm.verifyP192CombU)

end VG.Impl.Ecdsa.Arm.Fn
