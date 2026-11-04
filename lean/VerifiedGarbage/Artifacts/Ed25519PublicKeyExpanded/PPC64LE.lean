module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.PublicKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519 public-key derivation from the seed's SHA-512 digest -/

@[expose] public section

namespace VG.Artifacts.Ed25519PublicKeyExpanded.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed25519.publicKeyExpandedApi.artifact PPC64LE.target {
    consts := Impl.Ed25519.PPC64LE.combConsts
    code := Impl.Ed25519.PPC64LE.Whole.publicKeyExpandedCode
    stack := 224
    verified := Proof.Ed25519.PPC64LE.Whole.publicKeyExpanded_framed }]

end VG.Artifacts.Ed25519PublicKeyExpanded.PPC64LE
