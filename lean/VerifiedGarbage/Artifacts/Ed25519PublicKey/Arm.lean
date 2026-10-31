module

public import VerifiedGarbage.Proof.Ed25519.Arm.PublicKey.Verified
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ed25519PublicKey.Arm

def artifacts : List Artifact := [
  Spec.Ed25519.publicKeyApi.artifact Arm.target {
    consts := Impl.Ed25519.Arm.combConsts
    code := Impl.Ed25519.Arm.PublicKey.code
    stack := 280
    verified := Proof.Ed25519.Arm.PublicKey.publicKey_verified }]

end VG.Artifacts.Ed25519PublicKey.Arm
