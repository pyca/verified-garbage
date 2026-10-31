module

public import VerifiedGarbage.Proof.Scrypt.X86_64.Whole.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # scrypt (RFC 7914 §6) on x86-64, over SHA-256 -/

@[expose] public section

namespace VG.Generic.MdHash.X86_64.Scrypt

open VG.Proof.Scrypt.X86_64.Whole (pbkName pbkOf scrypt_verified scrypt_spSafe)

def artifacts (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
  match v.sha256 with
  | none => []
  | some c => [
    Spec.Scrypt.scryptApi.artifact X86_64.target {
      suffix := c.suffix
      code := Impl.Scrypt.X86_64.scrypt (pbkName c) (pbkOf c)
      stack := 88
      verified := scrypt_verified c
      spSafe := scrypt_spSafe c
      features := c.features }]

end VG.Generic.MdHash.X86_64.Scrypt
