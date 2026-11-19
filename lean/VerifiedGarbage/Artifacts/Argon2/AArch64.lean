module

public import VerifiedGarbage.Proof.Argon2.AArch64.DeriveVerified
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Argon2.AArch64.Scrub
public import VerifiedGarbage.Proof.Argon2.AArch64.HPrime.Verified
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.Blake2b.AArch64

/-! # Argon2 (RFC 9106) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Argon2.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.Blake2b.AArch64.variants.attach.flatMap
      fun (v : { v : Proof.Argon2.AArch64.HPrime.Backend // v ∈ VG.Proof.Variants.Blake2b.AArch64.variants }) => [
    Spec.Argon2.deriveApi.artifact VG.AArch64.target (VG.AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Impl.Argon2.AArch64.Derive.code ("vg_argon2_hprime" ++ v.1.suffix)
        v.1.hash
      verified := Proof.Argon2.AArch64.Derive.verified v.1 _
      spSafe := Proof.Argon2.AArch64.Derive.code_spSafe v.1 _ } Proof.Argon2.AArch64.Scrub.deriveClear
      (Proof.Argon2.AArch64.Scrub.deriveOk _) (Proof.Argon2.AArch64.Scrub.deriveSide v.1 v.2))]

end VG.Artifacts.Argon2.AArch64
