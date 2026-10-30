module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.VerifyVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's verification equation, on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Ed25519Verify.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed25519.verifyEquationApi.artifact PPC64LE.target {
    code := Impl.Ed25519.PPC64LE.verifyEquation
    verified := Proof.Ed25519.PPC64LE.verifyEquation_verified }]

end VG.Artifacts.Ed25519Verify.PPC64LE
