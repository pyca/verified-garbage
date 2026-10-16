module

public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! Baseline ARMv7 Ed25519 primitive with register saves in the reviewed scratch buffer. -/

@[expose] public section

namespace VG.Artifacts.Ed25519Scalar.Arm

def artifacts : List Artifact := [
  Spec.Ed25519.scalarReduceApi.artifact Arm.target {
    notes := ["Processes all 512 input bits with \
      sixteen 16-bit limbs, subtracting the subgroup order and selecting with a mask. \
      Callee-saved registers are saved in the first 32 bytes of `scratch`."]
    code := Impl.Ed25519.Arm.scalarReduce
    verified := Proof.Ed25519.Arm.scalarReduce_verified
    stack := 0 }]

end VG.Artifacts.Ed25519Scalar.Arm
