module

public import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Verified
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Impl.Mont.Mod
import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Spec.Rc2
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ed25519VerifyMessage.X86

def artifacts : List Artifact := [
  Spec.Ed25519.verifyApi.artifact X86.target {
    notes := ["Includes SHA-512 of R || A || message, challenge \
      reduction, and strict verification of the Ed25519 equation."]
    consts := Impl.Ed25519.X86.bConsts
    code := Impl.Ed25519.X86.VerifyMessage.code
    stack := 280
    verified := Proof.Ed25519.X86.VerifyMessage.verifyMessage_verified }]

end VG.Artifacts.Ed25519VerifyMessage.X86
