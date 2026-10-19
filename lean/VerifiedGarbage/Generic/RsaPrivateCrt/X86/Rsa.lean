module

public import VerifiedGarbage.Proof.Rsa.X86.PrivStackSafety
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rsa.X86.PrivVerified

/-! # Checked i686 private RSA follows every private CRT implementation -/

@[expose] public section
namespace VG.Generic.RsaPrivateCrt.X86.Rsa
open VG.Proof.Rsa.X86.PrivChecked

def artifacts (v : CrtImpl) : List Artifact := [
  Spec.Rsa.privateCheckedApi.artifact X86.target {
    suffix := v.suffix
    notes := ["Computes the private candidate using `" ++ v.name ++
      "`, checks it by public re-exponentiation using `" ++ v.pcName ++ "` and `" ++ v.pdName ++
      "`, and releases it only under the acceptance mask. All three calls and the comparison \
      follow a fixed schedule. The frame's candidate buffer is overwritten with zeros."]
    code := privCode v
    verified := code_verified v
    spSafe := code_sp v
    stack := stackBytes
    features := v.features }]

end VG.Generic.RsaPrivateCrt.X86.Rsa
