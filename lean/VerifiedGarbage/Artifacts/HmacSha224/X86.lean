module

public import VerifiedGarbage.Proof.Hmac.X86.Scrub
public import VerifiedGarbage.Impl.Hmac.X86
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.Sha256.X86

/-! # HMAC-SHA-224 (RFC 2104) on x86 -/

@[expose] public section

namespace VG.Artifacts.HmacSha224.X86

def artifacts : List Artifact :=
  VG.Proof.Variants.Sha256.X86.variants.flatMap fun (v : Proof.Sha256.X86.Variants.Backend) => [
    Spec.Hmac.sha224I.initAnyKeyApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.Hmac.X86.Fn.sha256Init v.M224 v.F224
      verified := Proof.Hmac.X86.Scrub.sha224_init_scrubbed v
      spSafe := Proof.Hmac.X86.Scrub.sha224_initSp v },
    Spec.Hmac.sha224I.finalizeApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.Hmac.X86.Fn.sha256Finalize v.M224
      verified := Proof.Hmac.X86.Scrub.sha224_fin_scrubbed v
      spSafe := Proof.Hmac.X86.Scrub.sha224_finSp v }]

end VG.Artifacts.HmacSha224.X86
