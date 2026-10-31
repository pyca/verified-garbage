module

public import VerifiedGarbage.Proof.Ed448.Arm.ScalarVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed448 scalar arithmetic on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Ed448Scalar.Arm

def artifacts : List Artifact := [
  Spec.Ed448.scalarReduceApi.artifact Arm.target {
    code := Impl.Ed448.Arm.scalarReduce
    verified := Proof.Ed448.Arm.scalarReduce_verified
    stack := 0 },
  Spec.Ed448.scalarMulAddApi.artifact Arm.target {
    code := Impl.Ed448.Arm.scalarMulAdd
    verified := Proof.Ed448.Arm.scalarMulAdd_verified
    stack := 0 }]

end VG.Artifacts.Ed448Scalar.Arm
