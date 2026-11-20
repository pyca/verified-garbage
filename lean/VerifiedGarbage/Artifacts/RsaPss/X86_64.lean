module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.QualifiedName
public import VerifiedGarbage.Proof.RsaPss.X86_64.Scrub
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86_64
public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.X86_64

/-! # RSASSA-PSS (RFC 8017) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.RsaPss.X86_64.RsaPrivateCrtAllMdHash

open VG.Proof.RsaPss.X86_64 (OK)
open VG.Proof.RsaPss.X86_64.Scrub (vs ts F G sign_scrubbed sign_spSafe)
open VG.Proof.RsaPkcs1Enc.X86_64 (privNameP privCodeP)

def artifacts (c : Proof.Rsa.X86_64.CrtImpl) : List Artifact :=
  if h : OK vs then [
    Spec.RsaPss.signPrecomputedMdTableApi.artifact X86_64.target {
      suffix := qualifiedName "" [("crt", c.suffix)]
      extra := c.extra
      tables := ts
      code := Impl.RsaPss.X86_64.Fn.signPrecomputed (Proof.Rsa.X86_64.PrivScrub.level c) F G (privNameP c) (privCodeP c)
      verified := .scrubbed (sign_scrubbed h c)
      spSafe := sign_spSafe h c }]
  else []

end VG.Artifacts.RsaPss.X86_64.RsaPrivateCrtAllMdHash

-- RSASSA-PSS verification on x86-64, with the hash functions as tables
namespace VG.Artifacts.RsaPss.X86_64.RsaPublicPrecomputedAllMdHash

open VG.Proof.RsaPss.X86_64 (OK)
open VG.Proof.RsaPss.X86_64.Scrub (vs ts F G verify_scrubbed verify_spSafe)

def artifacts (c : Proof.Rsa.X86_64.PublicImpl) : List Artifact :=
  if h : OK vs then [
    Spec.RsaPss.verifyPrecomputedMdTableApi.artifact X86_64.target {
      suffix := qualifiedName "" [("rsa", c.suffix)]
      tables := ts
      code := Impl.RsaPss.X86_64.Fn.verifyPrecomputed c.level F G c.name c.code
      verified := .scrubbed (verify_scrubbed h c)
      spSafe := verify_spSafe h c }]
  else []

end VG.Artifacts.RsaPss.X86_64.RsaPublicPrecomputedAllMdHash

namespace VG.Artifacts.RsaPss.X86_64

def artifacts : List Artifact :=
  (VG.Proof.Variants.RsaPrivateCrt.X86_64.variants.flatMap RsaPrivateCrtAllMdHash.artifacts) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.X86_64.variants.flatMap RsaPublicPrecomputedAllMdHash.artifacts)

end VG.Artifacts.RsaPss.X86_64
