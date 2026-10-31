module

public import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # The merged scalar multiply-add API, implemented with baseline integer instructions -/

@[expose] public section

namespace VG.Artifacts.Ed25519MulAdd.X86_64

def artifacts : List Artifact := [
  Spec.Ed25519.scalarMulAddApi.artifact X86_64.target {
    code := Impl.Ed25519.X86_64.scalarMulAdd
    verified := Proof.Ed25519.X86_64.scalarMulAdd_verified }]

end VG.Artifacts.Ed25519MulAdd.X86_64
