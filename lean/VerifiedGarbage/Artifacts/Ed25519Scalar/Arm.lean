module

public import VerifiedGarbage.Proof.Ed25519.Arm.ScalarVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! Baseline ARMv7 Ed25519 primitive with register saves in the reviewed scratch buffer. -/

@[expose] public section

namespace VG.Artifacts.Ed25519Scalar.Arm

def artifacts : List Artifact := [
  Spec.Ed25519.scalarReduceApi.artifact Arm.target {
    code := Impl.Ed25519.Arm.scalarReduce
    verified := Proof.Ed25519.Arm.scalarReduce_verified
    stack := 0 }]

end VG.Artifacts.Ed25519Scalar.Arm
