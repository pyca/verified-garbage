module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.Scrub
public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecVerified
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.DecP.Verified
public import VerifiedGarbage.Proof.Variants.Sha256.X86
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86
public import VerifiedGarbage.Proof.Framework.QualifiedName
public import VerifiedGarbage.Impl.RsaPkcs1Enc.X86.Front
public import VerifiedGarbage.Proof.RsaPkcs1Enc.X86.FrontScrub

/-! # RSAES-PKCS1-v1_5 (RFC 8017) on x86 -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Enc.X86

def direct : List (Artifact X86.target) := [
  Spec.RsaPkcs1Enc.encryptRandomApi.artifact VG.X86.target {
    code := Impl.RsaPkcs1Enc.X86.Fn.encryptRandom Proof.RsaPkcs1Enc.X86.Rnd.encName
      (Proof.RsaPkcs1Enc.X86.Rnd.enc Proof.RsaPkcs1Sig.X86.Ver.baseline)
    verified := Proof.RsaPkcs1Enc.X86.Scrub.encryptRandom_scrubbed }]

end VG.Artifacts.RsaPkcs1Enc.X86

-- RSAES-PKCS1-v1_5 decryption with implicit rejection on x86
namespace VG.Artifacts.RsaPkcs1Enc.X86.Sha256RsaPrivateCrt

open VG.Proof.Sha256.X86.Variants (Backend)
open VG.Proof.Rsa.X86.PrivChecked (CrtImpl)

def artifacts (v : Backend) (c : CrtImpl) : List (Artifact X86.target) := [
  Spec.RsaPkcs1Enc.decryptPrecomputedApi.artifact X86.target {
    suffix := qualifiedName "" [("sha256", v.stream.suffix), ("crt", c.suffix)]
    code := Impl.RsaPkcs1Enc.X86.Fn.decryptPrecomputed (Proof.RsaPkcs1Enc.X86.Front.bodyName v c)
      (Impl.RsaPkcs1Enc.X86.Decrypt.code v.F (Proof.RsaPkcs1Enc.X86.Dec.privNameP c)
        (Proof.Rsa.X86.PrivChecked.privCodeP c Proof.Rsa.X86.PrivChecked.crtPBaseline)
        Impl.RsaPkcs1Enc.X86.Decrypt.privArgsP)
    verified := Proof.RsaPkcs1Enc.X86.Front.front_scrubbed v c
    spSafe := Proof.RsaPkcs1Enc.X86.Front.front_scrubbed_spSafe v c }]

end VG.Artifacts.RsaPkcs1Enc.X86.Sha256RsaPrivateCrt

namespace VG.Artifacts.RsaPkcs1Enc.X86

def artifacts : List (Artifact X86.target) :=
  direct ++
  (VG.Proof.Variants.Sha256.X86.variants.flatMap fun v => VG.Proof.Variants.RsaPrivateCrt.X86.variants.flatMap fun v2 => Sha256RsaPrivateCrt.artifacts v v2)

end VG.Artifacts.RsaPkcs1Enc.X86
