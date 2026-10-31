module

public import VerifiedGarbage.Proof.Ed448.PPC64LE.ScalarVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed448 scalar arithmetic on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Ed448Scalar.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed448.scalarReduceApi.artifact PPC64LE.target {
    code := Impl.Ed448.PPC64LE.scalarReduce
    verified := Proof.Ed448.PPC64LE.scalarReduce_verified },
  Spec.Ed448.scalarMulAddApi.artifact PPC64LE.target {
    code := Impl.Ed448.PPC64LE.scalarMulAdd
    verified := Proof.Ed448.PPC64LE.scalarMulAdd_verified }]

end VG.Artifacts.Ed448Scalar.PPC64LE
