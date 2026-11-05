module

public import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.Expanded
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Ed25519 public-key derivation from the seed's SHA-512 digest -/

@[expose] public section

namespace VG.Artifacts.Ed25519PublicKeyExpanded.Arm

def artifacts : List Artifact := [
  Spec.Ed25519.publicKeyExpandedApi.artifact Arm.target {
    consts := Impl.Ed25519.Arm.combConsts
    code := Impl.Ed25519.Arm.PublicKey.codeExpanded
    stack := 280
    verified := Proof.Ed25519.Arm.PublicKey.publicKeyExpanded_verified }]

end VG.Artifacts.Ed25519PublicKeyExpanded.Arm
