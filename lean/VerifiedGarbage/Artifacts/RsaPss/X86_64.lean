module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaPss.MdTable
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.QualifiedName
import VerifiedGarbage.Proof.RsaPss.X86_64.Scrub
import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86_64
import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSASSA-PSS (RFC 8017) on x86-64 -/

namespace VG.Artifacts.RsaPss.X86_64.RsaPrivateCrtAllMdHash

open VG.Proof.RsaPss.X86_64 (OK)
open VG.Proof.RsaPss.X86_64.Scrub (vs ts F G sign_scrubbed sign_spSafe)
open VG.Proof.RsaPkcs1Enc.X86_64 (privNameP privCodeP)

def artifacts (c : Proof.Rsa.X86_64.CrtImpl) : List (Artifact X86_64.target) :=
  if h : OK vs then [
    Spec.RsaPss.signPrecomputedMdTableApi.artifact X86_64.target {
      suffix := qualifiedName "" [("crt", c.suffix)]
      extra := c.extra
      tables := ts
      code := Impl.RsaPss.X86_64.Fn.signPrecomputed (Proof.Rsa.X86_64.PrivScrub.level c) F G (privNameP c) (privCodeP c)
      verified := Proof.RsaPss.X86_64.Scrub.sign_scrubbed h c
      spSafe := Proof.RsaPss.X86_64.Scrub.sign_spSafe h c }]
  else []

end VG.Artifacts.RsaPss.X86_64.RsaPrivateCrtAllMdHash

-- RSASSA-PSS verification on x86-64, with the hash functions as tables
namespace VG.Artifacts.RsaPss.X86_64.RsaPublicPrecomputedAllMdHash

open VG.Proof.RsaPss.X86_64 (OK)
open VG.Proof.RsaPss.X86_64.Scrub (vs ts F G verify_scrubbed verify_spSafe)

def artifacts (c : Proof.Rsa.X86_64.PublicImpl) : List (Artifact X86_64.target) :=
  if h : OK vs then [
    Spec.RsaPss.verifyPrecomputedMdTableApi.artifact X86_64.target {
      suffix := qualifiedName "" [("rsa", c.suffix)]
      tables := ts
      code := Impl.RsaPss.X86_64.Fn.verifyPrecomputed c.level F G c.name c.code
      verified := Proof.RsaPss.X86_64.Scrub.verify_scrubbed h c
      spSafe := Proof.RsaPss.X86_64.Scrub.verify_spSafe h c }]
  else []

end VG.Artifacts.RsaPss.X86_64.RsaPublicPrecomputedAllMdHash

namespace VG.Artifacts.RsaPss.X86_64

public def artifacts : List (Artifact X86_64.target) :=
  (VG.Proof.Variants.RsaPrivateCrt.X86_64.variants.flatMap RsaPrivateCrtAllMdHash.artifacts) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.X86_64.variants.flatMap RsaPublicPrecomputedAllMdHash.artifacts)

spec_apis artifacts

end VG.Artifacts.RsaPss.X86_64
