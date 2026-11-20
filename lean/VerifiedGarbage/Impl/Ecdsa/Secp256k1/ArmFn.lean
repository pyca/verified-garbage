module

public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.ArmComb
public import VerifiedGarbage.Impl.Ecdsa.Arm.VerifyHash
public import VerifiedGarbage.Impl.Residue.Arm
public import VerifiedGarbage.Spec.Ecdsa.Verify.Secp256k1

/-!
# ECDSA over secp256k1 on 32-bit ARM, as emitted

`vg_ecdsa_secp256k1_verify` and its `_umaal` variant: each one's code, which keeps
the hash's working values in a frame of 96 bytes, then the instructions that
zero those bytes and set the registers a callee may change, but the result,
and the flags to constants (`Impl.Residue.Arm.scrubF`).
-/

@[expose] public section

namespace VG.Impl.Ecdsa.Arm.Fn

open VG.Arm VG.Impl.Residue.Arm

/-- `vg_ecdsa_secp256k1_verify`. -/
def verifySecp256k1 : Prog isa :=
  scrubF 32 96
    (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.Secp256k1.inst.curve.len false Impl.Ecdsa.Arm.verifySecp256k1Comb)

/-- `vg_ecdsa_secp256k1_verify_umaal`. -/
def verifySecp256k1U : Prog isa :=
  scrubF 32 96
    (Impl.Ecdsa.Arm.VerifyHash.verifyHash Spec.Ecdsa.Secp256k1.inst.curve.len false Impl.Ecdsa.Arm.verifySecp256k1CombU)

end VG.Impl.Ecdsa.Arm.Fn
