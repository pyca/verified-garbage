module

public import VerifiedGarbage.Proof.Scrypt.AArch64.Whole.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.Sha256Compress.AArch64

/-! # scrypt (RFC 7914) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Scrypt.AArch64

open VG.Proof.Scrypt.AArch64.Whole (pbkName pbkOf scrypt_verified)

def artifacts : List Artifact :=
  VG.Proof.Variants.Sha256Compress.AArch64.variants.flatMap fun (c : Proof.Sha256.AArch64.Compress) => [
    Spec.Scrypt.scryptApi.artifact AArch64.target {
        suffix := c.suffix
        code := Impl.Scrypt.AArch64.scrypt (pbkName c) (pbkOf c)
        stack := 96
        verified := scrypt_verified c }]

end VG.Artifacts.Scrypt.AArch64
