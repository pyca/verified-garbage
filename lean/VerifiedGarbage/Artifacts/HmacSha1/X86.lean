module

public import VerifiedGarbage.Proof.Hmac.X86.Scrub
public import VerifiedGarbage.Impl.Hmac.X86
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.Sha1.X86

/-! # HMAC-SHA-1 (RFC 2104) on x86 -/

@[expose] public section

namespace VG.Artifacts.HmacSha1.X86

def artifacts : List Artifact :=
  VG.Proof.Variants.Sha1.X86.variants.flatMap fun (v : Proof.Sha1.X86.Variants.Backend) => [
    Spec.Hmac.sha1I.initAnyKeyApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.Hmac.X86.Fn.sha1Init v.M v.F
      verified := .scrubbed (Proof.Hmac.X86.Scrub.sha1_init_scrubbed v)
      spSafe := Proof.Hmac.X86.Scrub.sha1_initSp v },
    Spec.Hmac.sha1I.finalizeApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.Hmac.X86.Fn.sha1Finalize v.M
      verified := .scrubbed (Proof.Hmac.X86.Scrub.sha1_fin_scrubbed v)
      spSafe := Proof.Hmac.X86.Scrub.sha1_finSp v }]

end VG.Artifacts.HmacSha1.X86
