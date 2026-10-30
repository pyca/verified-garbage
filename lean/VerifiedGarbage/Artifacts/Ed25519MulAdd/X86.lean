module

public import VerifiedGarbage.Proof.Ed25519.X86.MulAddVerified
import VerifiedGarbage.Proof.Ed25519.X86.MulAddLit
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ed25519MulAdd.X86

def artifacts : List Artifact := [
  Spec.Ed25519.scalarMulAddApi.artifact X86.target {
    code := Impl.Ed25519.X86.scalarMulAdd
    stack := 8
    verified := Proof.Ed25519.X86.scalarMulAdd_verified }]
end VG.Artifacts.Ed25519MulAdd.X86
