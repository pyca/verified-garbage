module

public import VerifiedGarbage.Proof.Ed448.AArch64.ScalarVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed448 scalar arithmetic on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Ed448Scalar.AArch64

def artifacts : List Artifact := [
  Spec.Ed448.scalarReduceApi.artifact AArch64.target {
    code := Impl.Ed448.AArch64.scalarReduce
    verified := Proof.Ed448.AArch64.scalarReduce_verified },
  Spec.Ed448.scalarMulAddApi.artifact AArch64.target {
    code := Impl.Ed448.AArch64.scalarMulAdd
    verified := Proof.Ed448.AArch64.scalarMulAdd_verified }]

end VG.Artifacts.Ed448Scalar.AArch64
