module

public import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519 scalar reduction on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Ed25519Scalar.X86_64

def artifacts : List Artifact := [
  Spec.Ed25519.scalarReduceApi.artifact X86_64.target {
    code := Impl.Ed25519.X86_64.scalarReduce
    verified := Proof.Ed25519.X86_64.scalarReduce_verified }]

end VG.Artifacts.Ed25519Scalar.X86_64
