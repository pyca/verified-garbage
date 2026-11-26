module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Argon2.Contract
import VerifiedGarbage.Proof.Argon2.X86.CompressVerified
import VerifiedGarbage.Proof.Argon2.X86.HPrime.Verified
import VerifiedGarbage.Proof.Argon2.X86.Derive.Verified
import VerifiedGarbage.Proof.Argon2.X86.CompressLit
import VerifiedGarbage.Proof.Blake2.X86.LitB
import VerifiedGarbage.Proof.Argon2.X86.Scrub
import VerifiedGarbage.Impl.Argon2.X86.Derive
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Argon2 (RFC 9106) on x86 -/

namespace VG.Artifacts.Argon2.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Argon2.deriveApi.artifact X86.target {
    code := Impl.Argon2.X86.Fn.derive
    verified := Proof.Argon2.X86.Scrub.derive_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Argon2.X86
