module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.AArch64
public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.AArch64

/-! # RSASSA-PKCS1-v1_5 on AArch64 -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Sig.AArch64

open VG.Proof.Rsa.AArch64 (PublicImpl CrtImpl)
open VG.Proof.RsaPkcs1Sig.AArch64

def artifacts : List Artifact :=
  (VG.Proof.Variants.RsaPrivateCrt.AArch64.variants.flatMap fun (v : CrtImpl) => [
    Spec.RsaPkcs1Sig.signPrecomputedApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.RsaPkcs1Sig.AArch64.Fn.signPrecomputed v.toCrt
      verified := signPrecomputed_scrubbed v }]) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.AArch64.variants.flatMap fun (v : PublicImpl) => [
    Spec.RsaPkcs1Sig.verifyPrecomputedApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.RsaPkcs1Sig.AArch64.Fn.verifyPrecomputed v.name v.code
      verified := verifyPrecomputed_scrubbed v },
    Spec.RsaPkcs1Sig.recoverPrecomputedApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.RsaPkcs1Sig.AArch64.Fn.recoverPrecomputed v.name v.code
      verified := recoverPrecomputed_scrubbed v }])

end VG.Artifacts.RsaPkcs1Sig.AArch64
