module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Spec.RsaOaep.MdTables
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.QualifiedName
public import VerifiedGarbage.Proof.RsaOaep.X86_64.Scrub
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86_64
public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.X86_64

/-! # RSAES-OAEP (RFC 8017) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.RsaOaep.X86_64.RsaPrivateCrtAllMdHash

open VG.Proof.RsaOaep.X86_64 (OK)
open VG.Proof.RsaOaep.X86_64.Scrub (vs ts dec_scrubbed dec_spSafe)
open VG.Proof.RsaPkcs1Enc.X86_64 (privNameP privCodeP)

def artifacts (c : Proof.Rsa.X86_64.CrtImpl) : List Artifact :=
  if h : OK vs then [
    Spec.RsaOaep.decryptPrecomputedMdTablesApi.artifact X86_64.target {
      suffix := qualifiedName "" [("crt", c.suffix)]
      extra := c.extra
      tables := ts
      code := Impl.RsaOaep.X86_64.Fn.decryptPrecomputed (Proof.Rsa.X86_64.PrivScrub.level c)
        (Proof.HashTable.X86_64.fnsOf vs) (privNameP c) (privCodeP c)
      verified := .scrubbed (dec_scrubbed h c)
      spSafe := dec_spSafe c }]
  else []

end VG.Artifacts.RsaOaep.X86_64.RsaPrivateCrtAllMdHash

-- RSAES-OAEP encryption with a precomputed public key on x86-64, with both hash functions as tables
namespace VG.Artifacts.RsaOaep.X86_64.RsaPublicPrecomputedAllMdHash

open VG.Proof.RsaOaep.X86_64 (OK)
open VG.Proof.RsaOaep.X86_64.Scrub (vs ts enc_scrubbed enc_spSafe)

def artifacts (c : Proof.Rsa.X86_64.PublicImpl) : List Artifact :=
  if h : OK vs then [
    Spec.RsaOaep.encryptMdTablesApi.artifact X86_64.target {
      suffix := qualifiedName "" [("rsa", c.suffix)]
      tables := ts
      code := Impl.RsaOaep.X86_64.Fn.encrypt c.level (Proof.HashTable.X86_64.fnsOf vs) c.name c.code
      verified := .scrubbed (enc_scrubbed h c)
      spSafe := enc_spSafe c }]
  else []

end VG.Artifacts.RsaOaep.X86_64.RsaPublicPrecomputedAllMdHash

namespace VG.Artifacts.RsaOaep.X86_64

def artifacts : List Artifact :=
  (VG.Proof.Variants.RsaPrivateCrt.X86_64.variants.flatMap RsaPrivateCrtAllMdHash.artifacts) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.X86_64.variants.flatMap RsaPublicPrecomputedAllMdHash.artifacts)

end VG.Artifacts.RsaOaep.X86_64
