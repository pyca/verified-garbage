module

public import VerifiedGarbage.Proof.Argon2.AArch64.DeriveVerified
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Verified
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.Blake2b.AArch64

/-! # Argon2 H′ for every ARM64 BLAKE2b backend -/

@[expose] public section

namespace VG.Artifacts.Argon2.AArch64

def artifactsFor (v : Proof.Argon2.AArch64.HPrime.Backend) : List Artifact := [
  Spec.Argon2.deriveApi.artifact VG.AArch64.target {
    suffix := v.suffix
    code := Impl.Argon2.AArch64.Derive.code ("vg_argon2_hprime" ++ v.suffix)
      v.hash
    stack := 400
    verified := Proof.Argon2.AArch64.Derive.verified v _
    spSafe := Proof.Argon2.AArch64.Derive.code_spSafe v _
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.Blake2b.AArch64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Argon2.AArch64
