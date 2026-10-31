module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.ScalarBaseVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's `[s] B`, encoded, on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Ed25519ScalarBase.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed25519.scalarBaseApi.artifact PPC64LE.target {
    code := Impl.Ed25519.PPC64LE.scalarBase
    verified := Proof.Ed25519.PPC64LE.scalarBase_verified }]

end VG.Artifacts.Ed25519ScalarBase.PPC64LE
