module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Hmac.Generic
import VerifiedGarbage.Proof.Hmac.X86.Scrub
import VerifiedGarbage.Impl.Hmac.X86
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.Sha256.X86
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # HMAC-SHA-256 (RFC 2104) on x86 -/

namespace VG.Artifacts.HmacSha256.X86

public def artifacts : List (Artifact X86.target) :=
  VG.Proof.Variants.Sha256.X86.variants.flatMap fun (v : Proof.Sha256.X86.Variants.Backend) => [
    Spec.Hmac.sha256I.initAnyKeyApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.Hmac.X86.Fn.sha256Init v.M v.F
      verified := Proof.Hmac.X86.Scrub.sha256_init_scrubbed v
      spSafe := Proof.Hmac.X86.Scrub.sha256_initSp v },
    Spec.Hmac.sha256I.finalizeApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.Hmac.X86.Fn.sha256Finalize v.M
      verified := Proof.Hmac.X86.Scrub.sha256_fin_scrubbed v
      spSafe := Proof.Hmac.X86.Scrub.sha256_finSp v }]

spec_apis artifacts

end VG.Artifacts.HmacSha256.X86
