module

public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Scrub
public import VerifiedGarbage.Impl.Pbkdf2.Whole.X86.Fn
public import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha1
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Frame
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.Hmac.Generic.Implies
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFin
public import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Loop
public import VerifiedGarbage.Proof.Sha1.X86.Stream.Variant
public import VerifiedGarbage.Proof.Sha256.X86.Stream.Variant
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha256
public import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
public import VerifiedGarbage.Proof.Variants.Sha256.X86

/-! # PBKDF2-HMAC-SHA-256 (RFC 8018) on x86 -/

@[expose] public section

namespace VG.Artifacts.Pbkdf2Sha256.X86

def artifacts : List Artifact :=
  VG.Proof.Variants.Sha256.X86.variants.flatMap fun (v : Proof.Sha256.X86.Variants.Backend) => [
    Spec.Hmac.sha256I.pbkdf2Api.artifact X86.target {
      suffix := v.suffix
      code := Impl.Pbkdf2.Whole.X86.Fn.sha256 v.F
      verified := Proof.Pbkdf2.Whole.X86.Scrub.sha256_scrubbed v
      spSafe := Proof.Pbkdf2.Whole.X86.Scrub.sha256_spSafe v }]

end VG.Artifacts.Pbkdf2Sha256.X86
