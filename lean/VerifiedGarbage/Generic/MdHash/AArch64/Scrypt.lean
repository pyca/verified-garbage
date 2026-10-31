module

public import VerifiedGarbage.Proof.Scrypt.AArch64.Whole.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # scrypt (RFC 7914 §6) on AArch64, over SHA-256 -/

@[expose] public section

namespace VG.Generic.MdHash.AArch64.Scrypt

open VG.Proof.Scrypt.AArch64.Whole (pbkName pbkOf scrypt_verified)

def artifacts (v : Proof.Pbkdf2.Md.AArch64.MdHash) : List Artifact :=
  match v.sha256 with
  | none => []
  | some c => [
    Spec.Scrypt.scryptApi.artifact AArch64.target {
      suffix := c.suffix
      code := Impl.Scrypt.AArch64.scrypt (pbkName c) (pbkOf c)
      stack := 96
      verified := scrypt_verified c
      features := c.features }]

end VG.Generic.MdHash.AArch64.Scrypt
