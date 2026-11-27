module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.Proof.Scrypt.AArch64.Whole.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.Sha256Compress.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # scrypt (RFC 7914) on AArch64 -/

namespace VG.Artifacts.Scrypt.AArch64

public def artifacts : List (Artifact AArch64.target) :=
  VG.Proof.Variants.Sha256Compress.AArch64.variants.flatMap fun (c : Proof.Sha256.AArch64.Compress) => [
    Spec.Scrypt.scryptApi.artifact AArch64.target {
      suffix := c.suffix
      code := Impl.Scrypt.AArch64.Fn.scrypt c.name c.suffix c.code
      verified := Proof.Scrypt.AArch64.Whole.scrypt_scrubbed c }]

spec_apis artifacts

end VG.Artifacts.Scrypt.AArch64
