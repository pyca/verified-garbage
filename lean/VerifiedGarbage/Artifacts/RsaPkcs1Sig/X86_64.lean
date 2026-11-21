module

public import VerifiedGarbage.Impl.RsaPkcs1Sig.X86_64.Fn
public import VerifiedGarbage.Proof.RsaPkcs1Sig.X86_64.Scrub
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86_64
public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.X86_64
public import VerifiedGarbage.TCB.X86_64.Print

/-! # RSASSA-PKCS1-v1_5 (RFC 8017) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Sig.X86_64

open VG.Proof.Rsa.X86_64 (PublicImpl)

open VG.Proof.Rsa.X86_64 (CrtImpl)
open VG.Proof.RsaPkcs1Sig.X86_64

def artifacts : List Artifact :=
  (VG.Proof.Variants.RsaPrivateCrt.X86_64.variants.flatMap fun (v : CrtImpl) => [
    Spec.RsaPkcs1Sig.signPrecomputedApi.artifact X86_64.target {
      suffix := v.suffix
      extra := v.extra
      code := Impl.RsaPkcs1Sig.X86_64.Fn.signPrecomputed (Scrub.signLevel v) (Sgn.privNameP v) (Sgn.privCodeP v)
      verified := .scrubbed (Scrub.sign_scrubbed v)
      spSafe := Scrub.sign_spSafe v }]) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.X86_64.variants.flatMap fun (v : PublicImpl) => [
    Spec.RsaPkcs1Sig.verifyPrecomputedApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.RsaPkcs1Sig.X86_64.Fn.verifyPrecomputed v.level v.name v.code
      verified := .scrubbed (Scrub.verify_scrubbed v)
      spSafe := Scrub.verify_spSafe v },
    Spec.RsaPkcs1Sig.recoverPrecomputedApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.RsaPkcs1Sig.X86_64.Fn.recoverPrecomputed v.level v.name v.code
      verified := .scrubbed (Scrub.recover_scrubbed v)
      spSafe := Scrub.recover_spSafe v }])

end VG.Artifacts.RsaPkcs1Sig.X86_64
