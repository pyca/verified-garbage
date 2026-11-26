module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaOaep.MdTables
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.QualifiedName
import VerifiedGarbage.Proof.RsaOaep.X86_64.Scrub
import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86_64
import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSAES-OAEP (RFC 8017) on x86-64 -/

namespace VG.Artifacts.RsaOaep.X86_64.RsaPrivateCrtAllMdHash

open VG.Proof.RsaOaep.X86_64 (OK)
open VG.Proof.RsaOaep.X86_64.Scrub (vs ts dec_scrubbed dec_spSafe)
open VG.Proof.RsaPkcs1Enc.X86_64 (privNameP privCodeP)

def artifacts (c : Proof.Rsa.X86_64.CrtImpl) : List (Artifact X86_64.target) :=
  if h : OK vs then [
    Spec.RsaOaep.decryptPrecomputedMdTablesApi.artifact X86_64.target {
      suffix := qualifiedName "" [("crt", c.suffix)]
      extra := c.extra
      tables := ts
      code := Impl.RsaOaep.X86_64.Fn.decryptPrecomputed (Proof.Rsa.X86_64.PrivScrub.level c)
        (Proof.HashTable.X86_64.fnsOf vs) (privNameP c) (privCodeP c)
      verified := Proof.RsaOaep.X86_64.Scrub.dec_scrubbed h c
      spSafe := Proof.RsaOaep.X86_64.Scrub.dec_spSafe c }]
  else []

end VG.Artifacts.RsaOaep.X86_64.RsaPrivateCrtAllMdHash

-- RSAES-OAEP encryption with a precomputed public key on x86-64, with both hash functions as tables
namespace VG.Artifacts.RsaOaep.X86_64.RsaPublicPrecomputedAllMdHash

open VG.Proof.RsaOaep.X86_64 (OK)
open VG.Proof.RsaOaep.X86_64.Scrub (vs ts enc_scrubbed enc_spSafe)

def artifacts (c : Proof.Rsa.X86_64.PublicImpl) : List (Artifact X86_64.target) :=
  if h : OK vs then [
    Spec.RsaOaep.encryptMdTablesApi.artifact X86_64.target {
      suffix := qualifiedName "" [("rsa", c.suffix)]
      tables := ts
      code := Impl.RsaOaep.X86_64.Fn.encrypt c.level (Proof.HashTable.X86_64.fnsOf vs) c.name c.code
      verified := Proof.RsaOaep.X86_64.Scrub.enc_scrubbed h c
      spSafe := Proof.RsaOaep.X86_64.Scrub.enc_spSafe c }]
  else []

end VG.Artifacts.RsaOaep.X86_64.RsaPublicPrecomputedAllMdHash

namespace VG.Artifacts.RsaOaep.X86_64

public def artifacts : List (Artifact X86_64.target) :=
  (VG.Proof.Variants.RsaPrivateCrt.X86_64.variants.flatMap RsaPrivateCrtAllMdHash.artifacts) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.X86_64.variants.flatMap RsaPublicPrecomputedAllMdHash.artifacts)

spec_apis artifacts

end VG.Artifacts.RsaOaep.X86_64
