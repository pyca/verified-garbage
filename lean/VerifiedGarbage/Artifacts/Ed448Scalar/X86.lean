module

public import VerifiedGarbage.Proof.Ed448.X86.ScalarVerified
import VerifiedGarbage.Proof.Ed448.X86.ScalarLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed448 scalar arithmetic on x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Ed448Scalar.X86

def artifacts : List Artifact := [
  Spec.Ed448.scalarReduceApi.artifact X86.target {
    code := Impl.Ed448.X86.scalarReduce
    verified := Proof.Ed448.X86.scalarReduce_verified },
  Spec.Ed448.scalarMulAddApi.artifact X86.target {
    code := Impl.Ed448.X86.scalarMulAdd
    verified := Proof.Ed448.X86.scalarMulAdd_verified }]

end VG.Artifacts.Ed448Scalar.X86
