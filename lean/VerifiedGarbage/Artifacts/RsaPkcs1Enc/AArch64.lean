module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.Sha256Compress.AArch64
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.AArch64
public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.AArch64
public import VerifiedGarbage.Proof.Framework.QualifiedName

/-! # RSAES-PKCS1-v1_5 (RFC 8017) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Enc.AArch64

open VG.Proof.RsaPkcs1Enc.AArch64.Scrub

def artifacts : List Artifact :=
  (VG.Proof.Variants.Sha256Compress.AArch64.variants.flatMap fun (h : Proof.Sha256.AArch64.Compress) =>
    VG.Proof.Variants.RsaPrivateCrt.AArch64.variants.flatMap fun (c : Proof.Rsa.AArch64.CrtImpl) => [
      Spec.RsaPkcs1Enc.decryptPrecomputedApi.artifact AArch64.target {
        suffix := qualifiedName "" [("sha256", h.suffix), ("crt", c.suffix)]
        code := Impl.RsaPkcs1Enc.AArch64.Fn.decryptPrecomputed h.name h.suffix h.code c.toCrt
        verified := .scrubbed (decryptPrecomputed_scrubbed h c) }]) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.AArch64.variants.flatMap fun (v : Proof.Rsa.AArch64.PublicImpl) => [
    Spec.RsaPkcs1Enc.encryptRandomApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.RsaPkcs1Enc.AArch64.Fn.encryptRandom v.suffix v.name v.code
      verified := .scrubbed (encryptRandom_scrubbed v) }])

end VG.Artifacts.RsaPkcs1Enc.AArch64
