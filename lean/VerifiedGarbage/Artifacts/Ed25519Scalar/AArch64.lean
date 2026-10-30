module

public import VerifiedGarbage.Proof.Ed25519.AArch64.ScalarVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# Ed25519 scalar reduction on AArch64

The signature and documentation come from the reviewed Ed25519 API.
This primitive reduces a 64-bit word at a time using baseline integer
instructions as part of the complete AArch64 signing and verification implementation.
-/

@[expose] public section

namespace VG.Artifacts.Ed25519Scalar.AArch64

def artifacts : List Artifact := [
  Spec.Ed25519.scalarReduceApi.artifact AArch64.target {
    code := Impl.Ed25519.AArch64.scalarReduce
    verified := Proof.Ed25519.AArch64.scalarReduce_verified }]

end VG.Artifacts.Ed25519Scalar.AArch64
