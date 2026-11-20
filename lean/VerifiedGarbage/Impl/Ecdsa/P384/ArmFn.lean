module

public import VerifiedGarbage.Impl.Ecdsa.P384.ArmComb
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.Impl.Residue.Arm
public import VerifiedGarbage.Spec.Ecdsa.Verify.P384

/-!
# ECDSA over P-384 on 32-bit ARM, as emitted

`vg_ecdsa_p384_verify` and its `_umaal` variant: each one's code, which keeps
the hash's working values in a frame of 96 bytes, then the instructions that
zero those bytes and set the registers a callee may change, but the result,
and the flags to constants (`Impl.Residue.Arm.scrubF`).
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_ecdsa_p384_verify`. -/
def verifyP384 : Prog isa :=
  scrubF 32 96
    (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P384.inst.curve.len false Impl.Ecdsa.Arm.verifyP384Comb)

/-- `vg_ecdsa_p384_verify_umaal`. -/
def verifyP384U : Prog isa :=
  scrubF 32 96
    (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P384.inst.curve.len false Impl.Ecdsa.Arm.verifyP384CombU)

end VG.Impl.Ecdsa.Arm.Fn
