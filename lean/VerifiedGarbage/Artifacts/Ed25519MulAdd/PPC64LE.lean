module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's `(r + k s) mod L`, on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Ed25519MulAdd.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed25519.scalarMulAddApi.artifact PPC64LE.target {
    code := Impl.Ed25519.PPC64LE.scalarMulAdd
    verified := Proof.Ed25519.PPC64LE.scalarMulAdd_verified }]

end VG.Artifacts.Ed25519MulAdd.PPC64LE
