module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.PublicKeyVerified
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ed25519PublicKey.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed25519.publicKeyApi.artifact PPC64LE.target {
    code := Impl.Ed25519.PPC64LE.Whole.publicKeyCode
    stack := 224
    verified := Proof.Ed25519.PPC64LE.Whole.publicKey_framed }]

end VG.Artifacts.Ed25519PublicKey.PPC64LE
