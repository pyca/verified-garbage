module

public import VerifiedGarbage.Proof.Scrypt.X86.Scrub
public import VerifiedGarbage.Impl.Scrypt.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.Sha256.X86

/-! # scrypt (RFC 7914) on x86 -/

@[expose] public section

namespace VG.Artifacts.Scrypt.X86

open VG.Proof.Scrypt.X86.Whole (pbkName pbkOf)

def artifacts : List Artifact :=
  VG.Proof.Variants.Sha256.X86.variants.flatMap fun (v : Proof.Sha256.X86.Variants.Backend) => [
    Spec.Scrypt.scryptApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.Scrypt.X86.Fn.scrypt (pbkName v) (pbkOf v)
      verified := .scrubbed (Proof.Scrypt.X86.Scrub.scrypt_scrubbed v)
      spSafe := VG.X86.Scrub.scrubAll_spSafe (Proof.Scrypt.X86.Whole.scrypt_spSafe v) }]

end VG.Artifacts.Scrypt.X86
