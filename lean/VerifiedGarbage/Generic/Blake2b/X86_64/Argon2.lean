module

public import VerifiedGarbage.Proof.Argon2.X86_64.HPrime.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Argon2 H′ for every x86-64 BLAKE2b backend -/

@[expose] public section

namespace VG.Generic.Blake2b.X86_64.Argon2

def artifacts (v : Proof.Blake2.X86_64.Backend) : List Artifact := [
  Spec.Argon2.hPrimeApi.artifact VG.X86_64.target {
    suffix := v.suffix
    code := Impl.Argon2.X86_64.HPrime.code (Proof.Argon2.X86_64.HPrime.hash v)
    stack := 16
    verified := Proof.Argon2.X86_64.HPrime.verified v
    spSafe := Proof.Argon2.X86_64.HPrime.spSafe v
    features := v.features }]

end VG.Generic.Blake2b.X86_64.Argon2
