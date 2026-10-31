module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.VerifyMsgVerified
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ed25519VerifyMessage.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed25519.verifyApi.artifact PPC64LE.target {
    code := Impl.Ed25519.PPC64LE.Whole.verifyCode
    stack := 272
    verified := Proof.Ed25519.PPC64LE.Whole.verify_framed }]

end VG.Artifacts.Ed25519VerifyMessage.PPC64LE
