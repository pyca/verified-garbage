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
  Spec.Argon2.deriveApi.artifact VG.AArch64.target {
    suffix := v.suffix
    code := Impl.Argon2.AArch64.Derive.code ("vg_argon2_hprime" ++ v.suffix)
      v.hash
    stack := 400
    verified := Proof.Argon2.AArch64.Derive.verified v _
    spSafe := Proof.Argon2.AArch64.Derive.code_spSafe v _
    features := v.features }]

end VG.Generic.Blake2b.AArch64.Argon2
