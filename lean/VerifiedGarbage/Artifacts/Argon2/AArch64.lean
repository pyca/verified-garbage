module

public import VerifiedGarbage.Proof.Argon2.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.Blake2b.AArch64

/-! # Argon2 (RFC 9106) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Argon2.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.Blake2b.AArch64.variants.flatMap fun (v : Proof.Argon2.AArch64.HPrime.Backend) => [
    Spec.Argon2.deriveApi.artifact VG.AArch64.target {
      suffix := v.suffix
      code := Impl.Argon2.AArch64.Derive.Fn.derive v.hash v.suffix
      verified := Proof.Argon2.AArch64.Scrub.derive_scrubbed v }]

end VG.Artifacts.Argon2.AArch64
