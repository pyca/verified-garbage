module

public import VerifiedGarbage.Proof.Scrypt.X86.Whole.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # scrypt (RFC 7914 §6) on x86, over SHA-256 -/

@[expose] public section

namespace VG.Generic.Sha256.X86.Scrypt

open VG.Proof.Scrypt.X86.Whole (pbkName pbkOf scrypt_verified scrypt_spSafe)

def artifacts (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  Spec.Scrypt.scryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.Scrypt.X86.scrypt (pbkName v) (pbkOf v)
    stack := 116
    verified := scrypt_verified v
    spSafe := scrypt_spSafe v
    features := v.features }]

end VG.Generic.Sha256.X86.Scrypt
