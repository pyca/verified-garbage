module

public import VerifiedGarbage.Impl.Ecdsa.P521.ArmComb
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.Impl.Residue.Arm
public import VerifiedGarbage.Spec.Ecdsa.Verify.P521

/-!
# ECDSA over P-521 on 32-bit ARM, as emitted

`vg_ecdsa_p521_verify` and its `_umaal` variant: each one's code, which keeps
the hash's working values in a frame of 96 bytes, then the instructions that
zero those bytes and set the registers a callee may change, but the result,
and the flags to constants (`Impl.Residue.Arm.scrubF`).
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_ecdsa_p521_verify`. -/
def verifyP521 : Prog isa :=
  scrubF 32 96
    (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true Impl.Ecdsa.Arm.verifyP521Comb)

/-- `vg_ecdsa_p521_verify_umaal`. -/
def verifyP521U : Prog isa :=
  scrubF 32 96
    (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.P521.inst.curve.len true Impl.Ecdsa.Arm.verifyP521CombU)

end VG.Impl.Ecdsa.Arm.Fn
