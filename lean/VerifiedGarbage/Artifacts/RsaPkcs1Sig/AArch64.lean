module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.AArch64
import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.AArch64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSASSA-PKCS1-v1_5 on AArch64 -/

namespace VG.Artifacts.RsaPkcs1Sig.AArch64

open VG.Proof.Rsa.AArch64 (PublicImpl CrtImpl)
open VG.Proof.RsaPkcs1Sig.AArch64

public def artifacts : List (Artifact AArch64.target) :=
  (VG.Proof.Variants.RsaPrivateCrt.AArch64.variants.flatMap fun (v : CrtImpl) => [
    Spec.RsaPkcs1Sig.signPrecomputedApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.RsaPkcs1Sig.AArch64.Fn.signPrecomputed v.toCrt
      verified := Proof.RsaPkcs1Sig.AArch64.signPrecomputed_scrubbed v }]) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.AArch64.variants.flatMap fun (v : PublicImpl) => [
    Spec.RsaPkcs1Sig.verifyPrecomputedApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.RsaPkcs1Sig.AArch64.Fn.verifyPrecomputed v.name v.code
      verified := Proof.RsaPkcs1Sig.AArch64.verifyPrecomputed_scrubbed v },
    Spec.RsaPkcs1Sig.recoverPrecomputedApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.RsaPkcs1Sig.AArch64.Fn.recoverPrecomputed v.name v.code
      verified := Proof.RsaPkcs1Sig.AArch64.recoverPrecomputed_scrubbed v }])

spec_apis artifacts

end VG.Artifacts.RsaPkcs1Sig.AArch64
