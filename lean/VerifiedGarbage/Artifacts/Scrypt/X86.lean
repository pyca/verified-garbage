module

public import VerifiedGarbage.Proof.Scrypt.X86.Whole.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.Sha256.X86

/-! # scrypt (RFC 7914 §6) on x86, over SHA-256 -/

@[expose] public section

namespace VG.Artifacts.Scrypt.X86

open VG.Proof.Scrypt.X86.Whole (pbkName pbkOf scrypt_verified scrypt_spSafe)

def artifactsFor (v : Proof.Sha256.X86.Variants.Backend) : List Artifact := [
  Spec.Scrypt.scryptApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.Scrypt.X86.scrypt (pbkName v) (pbkOf v)
    stack := 116
    verified := scrypt_verified v
    spSafe := scrypt_spSafe v
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.Sha256.X86.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Scrypt.X86
