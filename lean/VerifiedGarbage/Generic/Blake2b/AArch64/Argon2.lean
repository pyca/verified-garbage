module

public import VerifiedGarbage.Proof.Argon2.AArch64.DeriveVerified
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Verified

/-! # Argon2 H′ for every ARM64 BLAKE2b backend -/

@[expose] public section

namespace VG.Generic.Blake2b.AArch64.Argon2

def artifacts (v : Proof.Argon2.AArch64.HPrime.Backend) : List Artifact := [
  Spec.Argon2.hPrimeApi.artifact VG.AArch64.target {
    suffix := v.suffix
    notes := ["Calls the selected BLAKE2b streaming backend for every hash; \
        only argument handling, chaining, and output copying are specific to H′."]
    code := Impl.Argon2.AArch64.HPrime.code v.hash
    stack := 16
    verified := Proof.Argon2.AArch64.HPrime.verified v
    spSafe := Proof.Argon2.AArch64.HPrime.spSafe v
    features := v.features },
  Spec.Argon2.deriveApi.artifact VG.AArch64.target {
    suffix := v.suffix
    notes := ["Serial lane evaluation honors every positive worker limit. All hashing uses \
        the selected BLAKE2b streaming backend, including H₀ and every H′ call."]
    code := Impl.Argon2.AArch64.Derive.code (Spec.Argon2.hPrimeApi.name ++ v.suffix)
      v.hash
    stack := 400
    verified := Proof.Argon2.AArch64.Derive.verified v _
    spSafe := Proof.Argon2.AArch64.Derive.code_spSafe v _
    features := v.features }]

end VG.Generic.Blake2b.AArch64.Argon2
