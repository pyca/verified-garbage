module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Scrub
import VerifiedGarbage.Impl.Pbkdf2.Whole.X86.Fn
import VerifiedGarbage.Proof.Sha1.X86.Variants.Interface
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha1
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Frame
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Frame
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFin
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Loop
import VerifiedGarbage.Proof.Sha1.X86.Stream.Variant
import VerifiedGarbage.Proof.Sha256.X86.Stream.Variant
import VerifiedGarbage.Proof.Variants.Sha1.X86
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha256
import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
import VerifiedGarbage.Proof.Variants.Sha256.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # PBKDF2-HMAC-SHA-1 (RFC 8018) on x86 -/

namespace VG.Artifacts.Pbkdf2Sha1.X86

public def artifacts : List (Artifact X86.target) :=
  VG.Proof.Variants.Sha1.X86.variants.flatMap fun (v : Proof.Sha1.X86.Variants.Backend) => [
    Spec.Hmac.sha1I.pbkdf2Api.artifact X86.target {
      suffix := v.suffix
      code := Impl.Pbkdf2.Whole.X86.Fn.sha1 v.F
      verified := Proof.Pbkdf2.Whole.X86.Scrub.sha1_scrubbed v
      spSafe := Proof.Pbkdf2.Whole.X86.Scrub.sha1_spSafe v }]

spec_apis artifacts

end VG.Artifacts.Pbkdf2Sha1.X86
