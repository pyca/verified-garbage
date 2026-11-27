module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Scrub
import VerifiedGarbage.Impl.RsaPkcs1Enc.AArch64.Front
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.FrontScrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.Sha256Compress.AArch64
import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.AArch64
import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.AArch64
import VerifiedGarbage.Proof.Framework.QualifiedName
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSAES-PKCS1-v1_5 (RFC 8017) on AArch64 -/

namespace VG.Artifacts.RsaPkcs1Enc.AArch64

open VG.Proof.RsaPkcs1Enc.AArch64.Scrub

public def artifacts : List (Artifact AArch64.target) :=
  (VG.Proof.Variants.Sha256Compress.AArch64.variants.flatMap fun (h : Proof.Sha256.AArch64.Compress) =>
    VG.Proof.Variants.RsaPrivateCrt.AArch64.variants.flatMap fun (c : Proof.Rsa.AArch64.CrtImpl) => [
      Spec.RsaPkcs1Enc.decryptPrecomputedApi.artifact AArch64.target {
        suffix := qualifiedName "" [("sha256", h.suffix), ("crt", c.suffix)]
        code := Impl.RsaPkcs1Enc.AArch64.Fn.decryptPrecomputed (Proof.RsaPkcs1Enc.AArch64.Front.bodyName h c)
          (Proof.RsaPkcs1Enc.AArch64.Front.decCode h c)
        verified := Proof.RsaPkcs1Enc.AArch64.Front.front_scrubbed h c }]) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.AArch64.variants.flatMap fun (v : Proof.Rsa.AArch64.PublicImpl) => [
    Spec.RsaPkcs1Enc.encryptRandomApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.RsaPkcs1Enc.AArch64.Fn.encryptRandom v.suffix v.name v.code
      verified := Proof.RsaPkcs1Enc.AArch64.Scrub.encryptRandom_scrubbed v
      publicOutOk := Proof.RsaPkcs1Enc.AArch64.Scrub.encryptRandom_public v }])

spec_apis artifacts

end VG.Artifacts.RsaPkcs1Enc.AArch64
