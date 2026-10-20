module

public import VerifiedGarbage.Proof.Argon2.X86.CompressVerified
public import VerifiedGarbage.Proof.Argon2.X86.HPrime.Verified
public import VerifiedGarbage.Proof.Argon2.X86.Derive.Verified
import VerifiedGarbage.Proof.Argon2.X86.CompressLit
import VerifiedGarbage.Proof.Blake2.X86.LitB
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Argon2 (RFC 9106) on x86 -/

@[expose] public section

namespace VG.Artifacts.Argon2.X86

def artifacts : List Artifact := [
  Spec.Argon2.compressApi.artifact X86.target {
    code := Impl.Argon2.X86.compress
    stack := 0
    verified := Proof.Argon2.X86.compressShared_verified },
  Spec.Argon2.hPrimeApi.artifact X86.target {
    code := Impl.Argon2.X86.HPrime.code
    stack := 60
    verified := Proof.Argon2.X86.HPrime.hPrimeShared_verified },
  Spec.Argon2.deriveApi.artifact X86.target {
    code := Impl.Argon2.X86.Derive.derive
    stack := 244
    verified := Proof.Argon2.X86.Derive.deriveShared_verified }]

end VG.Artifacts.Argon2.X86
