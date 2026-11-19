module

public import VerifiedGarbage.Proof.Scrypt.AArch64.Whole.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Scrypt.AArch64.Scrub
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.Sha256Compress.AArch64

/-! # scrypt (RFC 7914) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Scrypt.AArch64

open VG.Proof.Scrypt.AArch64.Whole (pbkName pbkOf scrypt_verified)

def artifacts : List Artifact :=
  VG.Proof.Variants.Sha256Compress.AArch64.variants.attach.flatMap
      fun (c : { c : Proof.Sha256.AArch64.Compress // c ∈ VG.Proof.Variants.Sha256Compress.AArch64.variants }) => [
    Spec.Scrypt.scryptApi.artifact AArch64.target (VG.AArch64.ScrubAll.scrubAllOf {
        suffix := c.1.suffix
        code := Impl.Scrypt.AArch64.scrypt (pbkName c.1) (pbkOf c.1)
        verified := scrypt_verified c.1 }
      (VG.AArch64.ScrubAll.clearUnion Proof.Scrypt.AArch64.Scrub.scryptOwn c.1.clear)
      (Proof.Scrypt.AArch64.Scrub.scryptOk _) (Proof.Scrypt.AArch64.Scrub.scryptSide c.1 c.2))]

end VG.Artifacts.Scrypt.AArch64
