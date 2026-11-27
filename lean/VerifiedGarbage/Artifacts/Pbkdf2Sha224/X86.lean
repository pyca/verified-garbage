module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Pbkdf2.Generic
public import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Scrub
import VerifiedGarbage.Impl.Pbkdf2.Whole.X86.Fn
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha224
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Frame
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Frame
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sha256.X86.Variants.Interface
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.HmacFin
import VerifiedGarbage.Proof.Pbkdf2.Md.X86.Instances
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Loop
import VerifiedGarbage.Proof.Pbkdf2.Whole.X86.Sha256
import VerifiedGarbage.Proof.Sha256.X86.Stream.Variant
import VerifiedGarbage.Proof.Variants.Sha256.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # PBKDF2-HMAC-SHA-224 (RFC 8018) on x86 -/

namespace VG.Artifacts.Pbkdf2Sha224.X86

public def artifacts : List (Artifact X86.target) :=
  VG.Proof.Variants.Sha256.X86.variants.flatMap fun (v : Proof.Sha256.X86.Variants.Backend) => [
    Spec.Hmac.sha224I.pbkdf2Api.artifact X86.target {
      suffix := v.suffix
      code := Impl.Pbkdf2.Whole.X86.Fn.sha256 v.F224
      verified := Proof.Pbkdf2.Whole.X86.Scrub.sha224_scrubbed v
      spSafe := Proof.Pbkdf2.Whole.X86.Scrub.sha224_spSafe v }]

spec_apis artifacts

end VG.Artifacts.Pbkdf2Sha224.X86
