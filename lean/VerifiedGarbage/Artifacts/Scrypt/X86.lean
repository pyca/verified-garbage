module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.Proof.Scrypt.X86.Scrub
import VerifiedGarbage.Impl.Scrypt.X86.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.Sha256.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # scrypt (RFC 7914) on x86 -/

namespace VG.Artifacts.Scrypt.X86

open VG.Proof.Scrypt.X86.Whole (pbkName pbkOf)

public def artifacts : List (Artifact X86.target) :=
  VG.Proof.Variants.Sha256.X86.variants.flatMap fun (v : Proof.Sha256.X86.Variants.Backend) => [
    Spec.Scrypt.scryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.Scrypt.X86.Fn.scrypt (pbkName v) (pbkOf v)
      verified := Proof.Scrypt.X86.Scrub.scrypt_scrubbed v
      spSafe := Proof.Scrypt.X86.Scrub.scrypt_spSafeFn v }]

spec_apis artifacts

end VG.Artifacts.Scrypt.X86
