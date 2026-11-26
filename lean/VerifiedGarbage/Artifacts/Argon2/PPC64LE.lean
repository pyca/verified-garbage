module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.PPC64LE.Compress
import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.CT
import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Verified
import VerifiedGarbage.Proof.Argon2.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Argon2 (RFC 9106) on PPC64LE -/

namespace VG.Artifacts.Argon2.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Argon2.deriveApi.artifact PPC64LE.target {
    code := Impl.Argon2.PPC64LE.Fn.derive
    verified := Proof.Argon2.PPC64LE.Scrub.derive_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Argon2.PPC64LE
