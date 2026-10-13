module

public import VerifiedGarbage.Proof.Ed25519.X86.VerifyMessage.Verified
import VerifiedGarbage.Proof.Framework.TaintSum
import VerifiedGarbage.Impl.Mont.Mod
import VerifiedGarbage.Proof.Framework.X86.TaintMono
import VerifiedGarbage.Proof.MdStream.Spec
import VerifiedGarbage.Spec.Rc2

@[expose] public section

namespace VG.Artifacts.Ed25519VerifyMessage.X86

def artifacts : List Artifact := [
  { Spec.Ed25519.verifyApi with
    target := X86.target
    doc := Spec.Ed25519.verifyApi.doc (notes := ["Includes SHA-512 of R || A || message, challenge \
      reduction, and strict verification of the Ed25519 equation."])
    consts := Impl.Ed25519.X86.bConsts
    code := Impl.Ed25519.X86.VerifyMessage.code
    contract := Spec.Ed25519.verifyContract (X86.abi.withConsts Impl.Ed25519.X86.bConsts) 280
    stack := 280
    verified := Proof.Ed25519.X86.VerifyMessage.verifyMessage_verified
    spSafe := Code.all_of_allInstrs (by lit_decide) }]

end VG.Artifacts.Ed25519VerifyMessage.X86
