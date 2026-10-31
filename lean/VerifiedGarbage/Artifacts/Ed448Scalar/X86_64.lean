module

public import VerifiedGarbage.Proof.Ed448.X86_64.ScalarVerified
import VerifiedGarbage.Proof.Ed448.X86_64.ScalarLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed448 scalar arithmetic on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Ed448Scalar.X86_64

def artifacts : List Artifact := [
  Spec.Ed448.scalarReduceApi.artifact X86_64.target {
    code := Impl.Ed448.X86_64.scalarReduce
    verified := Proof.Ed448.X86_64.scalarReduce_verified },
  Spec.Ed448.scalarMulAddApi.artifact X86_64.target {
    code := Impl.Ed448.X86_64.scalarMulAdd
    verified := Proof.Ed448.X86_64.scalarMulAdd_verified }]

end VG.Artifacts.Ed448Scalar.X86_64
