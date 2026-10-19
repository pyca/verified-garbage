module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86.SignStackSafety
public import VerifiedGarbage.Proof.Framework.Registration

/-! # PKCS #1 signing follows every i686 private CRT implementation -/

@[expose] public section
namespace VG.Generic.RsaPrivateCrt.X86.RsaPkcs1Sig
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl privCode)
open VG.Proof.RsaPkcs1Sig.X86.Sgn

def artifacts (v : CrtImpl) : List Artifact := [
  Spec.RsaPkcs1Sig.signApi.artifact X86.target {
    suffix := v.suffix
    notes := ["Encodes the digest in a private frame, signs it with `" ++ privName v ++
      "`, and overwrites the encoding with zeros. Only public lengths, the hash identifier, \
      and the public key affect branches and addresses."]
    code := Impl.RsaPkcs1Sig.X86.Sign.code (privName v) (privCode v)
    stack := sigStack
    verified := sign_verified v
    spSafe := code_sp v
    features := v.features }]

end VG.Generic.RsaPrivateCrt.X86.RsaPkcs1Sig
