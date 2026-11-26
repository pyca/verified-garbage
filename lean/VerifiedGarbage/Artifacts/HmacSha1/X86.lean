module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Hmac.X86.Scrub
import VerifiedGarbage.Impl.Hmac.X86
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.Sha1.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # HMAC-SHA-1 (RFC 2104) on x86 -/

namespace VG.Artifacts.HmacSha1.X86

public def artifacts : List (Artifact X86.target) :=
  VG.Proof.Variants.Sha1.X86.variants.flatMap fun (v : Proof.Sha1.X86.Variants.Backend) => [
    Spec.Hmac.sha1I.initAnyKeyApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.Hmac.X86.Fn.sha1Init v.M v.F
      verified := Proof.Hmac.X86.Scrub.sha1_init_scrubbed v
      spSafe := Proof.Hmac.X86.Scrub.sha1_initSp v },
    Spec.Hmac.sha1I.finalizeApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.Hmac.X86.Fn.sha1Finalize v.M
      verified := Proof.Hmac.X86.Scrub.sha1_fin_scrubbed v
      spSafe := Proof.Hmac.X86.Scrub.sha1_finSp v }]

spec_apis artifacts

end VG.Artifacts.HmacSha1.X86
