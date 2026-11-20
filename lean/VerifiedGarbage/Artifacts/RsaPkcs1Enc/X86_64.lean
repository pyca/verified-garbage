module

public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86_64.Fn
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Scrub
public import VerifiedGarbage.Proof.Variants.Sha256Compress.X86_64
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86_64
public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.X86_64
public import VerifiedGarbage.Proof.Framework.QualifiedName
public import VerifiedGarbage.TCB.X86_64.Print

/-! # RSAES-PKCS1-v1_5 (RFC 8017) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Enc.X86_64.Sha256RsaPrivateCrt

open VG.Proof.RsaPkcs1Enc.X86_64.Dec (HH)

def artifacts (h : Proof.Sha256.X86_64.Compress) (c : Proof.Rsa.X86_64.CrtImpl) : List Artifact :=
  [
    Spec.RsaPkcs1Enc.decryptPrecomputedApi.artifact X86_64.target {
      suffix := qualifiedName "" [("sha256", h.suffix), ("crt", c.suffix)]
      extra := c.extra
      code := Impl.RsaPkcs1Enc.X86_64.Fn.decryptPrecomputed (Proof.RsaPkcs1Enc.X86_64.Scrub.decLevel h c) (HH h)
        (VG.Proof.RsaPkcs1Enc.X86_64.Dec.privNameP c) (VG.Proof.RsaPkcs1Enc.X86_64.Dec.privCodeP c)
      verified := .scrubbed (Proof.RsaPkcs1Enc.X86_64.Scrub.dec_scrubbed h c)
      spSafe := Proof.RsaPkcs1Enc.X86_64.Scrub.dec_spSafe h c }]

end VG.Artifacts.RsaPkcs1Enc.X86_64.Sha256RsaPrivateCrt

namespace VG.Artifacts.RsaPkcs1Enc.X86_64

open VG.Proof.Rsa.X86_64 (PublicImpl)
open VG.Proof.RsaPkcs1Enc.X86_64

def artifacts : List Artifact :=
  (VG.Proof.Variants.Sha256Compress.X86_64.variants.flatMap fun v => VG.Proof.Variants.RsaPrivateCrt.X86_64.variants.flatMap fun v2 => Sha256RsaPrivateCrt.artifacts v v2) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.X86_64.variants.flatMap fun (v : PublicImpl) => [
    Spec.RsaPkcs1Enc.encryptRandomApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.RsaPkcs1Enc.X86_64.Fn.encryptRandom v.level (Rnd.encName v) (Rnd.encCode v)
      verified := .scrubbed (Proof.RsaPkcs1Enc.X86_64.Scrub.rnd_scrubbed v)
      spSafe := Proof.RsaPkcs1Enc.X86_64.Scrub.rnd_spSafe v }])

end VG.Artifacts.RsaPkcs1Enc.X86_64
