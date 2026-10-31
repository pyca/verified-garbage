module

public import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Ed25519 scalar reduction on x86-64

The signature and documentation come from the reviewed Ed25519 API.
This building block reduces a 64-bit word at a time using baseline integer
instructions; it neither hashes messages nor implements signing by itself.
-/

@[expose] public section

namespace VG.Artifacts.Ed25519Scalar.X86_64

def artifacts : List Artifact := [
  Spec.Ed25519.scalarReduceApi.artifact X86_64.target {
    code := Impl.Ed25519.X86_64.scalarReduce
    verified := Proof.Ed25519.X86_64.scalarReduce_verified }]

end VG.Artifacts.Ed25519Scalar.X86_64
