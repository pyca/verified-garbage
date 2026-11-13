module

public import VerifiedGarbage.Proof.Scrypt.X86_64.Whole.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.Sha256Compress.X86_64
public import VerifiedGarbage.Proof.Variants.ScryptRoMix.X86_64

/-! # scrypt (RFC 7914) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Scrypt.X86_64

open VG.Proof.Scrypt.X86_64.Whole (pbkName pbkOf scrypt_verified scrypt_spSafe scrypt_postOut)

def artifacts : List Artifact :=
  VG.Proof.Variants.ScryptRoMix.X86_64.variants.flatMap fun (R : Proof.Scrypt.X86_64.Whole.RMImpl) =>
  VG.Proof.Variants.Sha256Compress.X86_64.variants.flatMap fun (c : Proof.Sha256.X86_64.Compress) => [
    Spec.Scrypt.scryptApi.artifact X86_64.target (X86_64.Scrub.withScrubAll {
        suffix := c.suffix ++ R.suffix
        notWith := R.notWith
        code := Impl.Scrypt.X86_64.scrypt R.name R.code (pbkName c) (pbkOf c)
        stack := 88
        verified := scrypt_verified c R
        spSafe := scrypt_spSafe c R } (scrypt_postOut 88))]

end VG.Artifacts.Scrypt.X86_64
