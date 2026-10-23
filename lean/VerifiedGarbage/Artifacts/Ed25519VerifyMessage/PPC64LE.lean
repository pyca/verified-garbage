module

public import VerifiedGarbage.Proof.Ed25519.PPC64LE.Whole.VerifyMsgVerified
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ed25519VerifyMessage.PPC64LE

def artifacts : List Artifact := [
  Spec.Ed25519.verifyApi.artifact PPC64LE.target {
    notes := ["Includes SHA-512 of R || A || message (calls of SHA-512's streaming functions), \
      challenge reduction (a call of `vg_ed25519_scalar_reduce`), and strict verification of the \
      Ed25519 equation (a call of `vg_ed25519_verify_equation`). The challenge, its digest, the \
      saved nonvolatile registers and `lr` are in a frame of 224 bytes on the stack."]
    code := Impl.Ed25519.PPC64LE.Whole.verifyCode
    stack := 272
    verified := Proof.Ed25519.PPC64LE.Whole.verify_framed }]

end VG.Artifacts.Ed25519VerifyMessage.PPC64LE
