module

public import VerifiedGarbage.Proof.Ed25519.Arm.VerifyMessage.Verified
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ed25519VerifyMessage.Arm

def artifacts : List Artifact := [
  Spec.Ed25519.verifyApi.artifact Arm.target {
    code := Impl.Ed25519.Arm.VerifyMessage.code
    stack := 280
    verified := Proof.Ed25519.Arm.VerifyMessage.verifyMessage_verified }]

end VG.Artifacts.Ed25519VerifyMessage.Arm
