module

public import VerifiedGarbage.Proof.Argon2.PPC64LE.Compress
public import VerifiedGarbage.Proof.Argon2.PPC64LE.HPrime.CT
public import VerifiedGarbage.Proof.Argon2.PPC64LE.Derive.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Argon2 (RFC 9106) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Argon2.PPC64LE

def artifacts : List Artifact := [
  Spec.Argon2.compressApi.artifact PPC64LE.target {
    code := Impl.Argon2.PPC64LE.compress
    verified := Proof.Argon2.PPC64LE.compress_verified },
  Spec.Argon2.hPrimeApi.artifact PPC64LE.target {
    code := Impl.Argon2.PPC64LE.HPrime.code
    stack := 48
    verified := Proof.Argon2.PPC64LE.HPrime.verified },
  Spec.Argon2.deriveApi.artifact PPC64LE.target {
    code := Impl.Argon2.PPC64LE.Derive.derive
    stack := 384
    verified := Proof.Argon2.PPC64LE.Derive.deriveShared_verified }]

end VG.Artifacts.Argon2.PPC64LE
