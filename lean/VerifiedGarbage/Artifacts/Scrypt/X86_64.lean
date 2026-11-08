module

public import VerifiedGarbage.Proof.Scrypt.X86_64.Whole.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.MdHash.X86_64

/-! # scrypt (RFC 7914 §6) on x86-64, over SHA-256 -/

@[expose] public section

namespace VG.Artifacts.Scrypt.X86_64

open VG.Proof.Scrypt.X86_64.Whole (pbkName pbkOf scrypt_verified scrypt_spSafe)

def artifactsFor (v : Proof.Pbkdf2.Md.X86_64.MdHash) : List Artifact :=
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

def artifacts : List Artifact :=
  VG.Proof.Variants.MdHash.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Scrypt.X86_64
