module

public import VerifiedGarbage.Proof.Argon2.X86.CompressVerified
public import VerifiedGarbage.Proof.Argon2.X86.HPrime.Verified
public import VerifiedGarbage.Proof.Argon2.X86.Derive.Verified
import VerifiedGarbage.Proof.Argon2.X86.CompressLit
import VerifiedGarbage.Proof.Blake2.X86.LitB
public import VerifiedGarbage.Proof.Argon2.X86.Scrub
public import VerifiedGarbage.Impl.Argon2.X86.Derive
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # Argon2 (RFC 9106) on x86 -/

@[expose] public section

namespace VG.Artifacts.Argon2.X86

def artifacts : List Artifact := [
  Spec.Argon2.deriveApi.artifact X86.target {
    code := Impl.Argon2.X86.Fn.derive
    verified := Proof.Argon2.X86.Scrub.derive_scrubbed }]

end VG.Artifacts.Argon2.X86
