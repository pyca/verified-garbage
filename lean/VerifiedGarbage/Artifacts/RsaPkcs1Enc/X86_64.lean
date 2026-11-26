module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Random
import VerifiedGarbage.Impl.RsaPkcs1Enc.X86_64.Fn
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.Scrub
import VerifiedGarbage.Impl.RsaPkcs1Enc.X86_64.Front
import VerifiedGarbage.Proof.RsaPkcs1Enc.X86_64.FrontScrub
import VerifiedGarbage.Proof.Variants.Sha256Compress.X86_64
import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86_64
import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.X86_64
import VerifiedGarbage.Proof.Framework.QualifiedName
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSAES-PKCS1-v1_5 (RFC 8017) on x86-64 -/

namespace VG.Artifacts.RsaPkcs1Enc.X86_64.Sha256RsaPrivateCrt

open VG.Proof.RsaPkcs1Enc.X86_64.Dec (HH)

def artifacts (h : Proof.Sha256.X86_64.Compress) (c : Proof.Rsa.X86_64.CrtImpl) :
    List (Artifact X86_64.target) :=
  [
    Spec.RsaPkcs1Enc.decryptPrecomputedApi.artifact X86_64.target {
      suffix := qualifiedName "" [("sha256", h.suffix), ("crt", c.suffix)]
      extra := c.extra
      code := Impl.RsaPkcs1Enc.X86_64.Fn.decryptPrecomputed (Proof.RsaPkcs1Enc.X86_64.Scrub.decLevel h c)
        (Proof.RsaPkcs1Enc.X86_64.Front.bodyName h c) (Impl.RsaPkcs1Enc.X86_64.Decrypt.codeP (HH h)
          (VG.Proof.RsaPkcs1Enc.X86_64.Dec.privNameP c) (VG.Proof.RsaPkcs1Enc.X86_64.Dec.privCodeP c))
      verified := Proof.RsaPkcs1Enc.X86_64.Front.front_scrubbed h c
      spSafe := Proof.RsaPkcs1Enc.X86_64.Front.front_scrubbed_spSafe h c }]

end VG.Artifacts.RsaPkcs1Enc.X86_64.Sha256RsaPrivateCrt

namespace VG.Artifacts.RsaPkcs1Enc.X86_64

open VG.Proof.Rsa.X86_64 (PublicImpl)
open VG.Proof.RsaPkcs1Enc.X86_64

public def artifacts : List (Artifact X86_64.target) :=
  (VG.Proof.Variants.Sha256Compress.X86_64.variants.flatMap fun v => VG.Proof.Variants.RsaPrivateCrt.X86_64.variants.flatMap fun v2 => Sha256RsaPrivateCrt.artifacts v v2) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.X86_64.variants.flatMap fun (v : PublicImpl) => [
    Spec.RsaPkcs1Enc.encryptRandomApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.RsaPkcs1Enc.X86_64.Fn.encryptRandom v.level (Rnd.encName v) (Rnd.encCode v)
      verified := Proof.RsaPkcs1Enc.X86_64.Scrub.rnd_scrubbed v
      publicOutOk := Proof.RsaPkcs1Enc.X86_64.Scrub.rnd_public v
      spSafe := Proof.RsaPkcs1Enc.X86_64.Scrub.rnd_spSafe v }])

spec_apis artifacts

end VG.Artifacts.RsaPkcs1Enc.X86_64
