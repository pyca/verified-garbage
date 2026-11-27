module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.Blake2b.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Argon2 (RFC 9106) on AArch64 -/

namespace VG.Artifacts.Argon2.AArch64

public def artifacts : List (Artifact AArch64.target) :=
  VG.Proof.Variants.Blake2b.AArch64.variants.flatMap fun (v : Proof.Argon2.AArch64.HPrime.Backend) => [
    Spec.Argon2.deriveApi.artifact VG.AArch64.target {
      suffix := v.suffix
      code := Impl.Argon2.AArch64.Derive.Fn.derive v.hash v.suffix
      verified := Proof.Argon2.AArch64.Scrub.derive_scrubbed v }]

spec_apis artifacts

end VG.Artifacts.Argon2.AArch64
