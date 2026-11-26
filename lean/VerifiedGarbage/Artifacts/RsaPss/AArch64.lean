module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaPss.MdTable
import VerifiedGarbage.Proof.RsaPss.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.AArch64
import VerifiedGarbage.Proof.Variants.MdHash.AArch64
import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.AArch64
import VerifiedGarbage.Proof.Framework.QualifiedName
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSASSA-PSS (RFC 8017) on AArch64 -/

namespace VG.Artifacts.RsaPss.AArch64.RsaPrivateCrtAllMdHash

open VG.Proof.MdHashTable.AArch64 (tables)
open VG.Proof.Variants.MdHash.AArch64 (variants hashes)

def artifacts (c : Proof.Rsa.AArch64.CrtImpl) : List (Artifact AArch64.target) := [
  Spec.RsaPss.signPrecomputedMdTableApi.artifact AArch64.target {
    suffix := qualifiedName "" [("crt", c.suffix)]
    tables := [("hash", tables variants), ("mgf1", tables variants)]
    code := Impl.RsaPss.AArch64.Fn.signCP hashes c.toCrt
    verified := Proof.RsaPss.AArch64.Scrub.signCP_scrubbed c }]

end VG.Artifacts.RsaPss.AArch64.RsaPrivateCrtAllMdHash

-- RSASSA-PSS verification on AArch64 with a precomputed key, with the hash functions as tables
namespace VG.Artifacts.RsaPss.AArch64.RsaPublicPrecomputedAllMdHash

open VG.Proof.MdHashTable.AArch64 (tables)
open VG.Proof.Variants.MdHash.AArch64 (variants hashes)

def artifacts (c : Proof.Rsa.AArch64.PublicImpl) : List (Artifact AArch64.target) := [
  Spec.RsaPss.verifyPrecomputedMdTableApi.artifact AArch64.target {
    suffix := qualifiedName "" [("rsa", c.suffix)]
    tables := [("hash", tables variants), ("mgf1", tables variants)]
    code := Impl.RsaPss.AArch64.Fn.verifyC hashes c.name c.code
    verified := Proof.RsaPss.AArch64.Scrub.verifyC_scrubbed c }]

end VG.Artifacts.RsaPss.AArch64.RsaPublicPrecomputedAllMdHash

namespace VG.Artifacts.RsaPss.AArch64

public def artifacts : List (Artifact AArch64.target) :=
  (VG.Proof.Variants.RsaPrivateCrt.AArch64.variants.flatMap RsaPrivateCrtAllMdHash.artifacts) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.AArch64.variants.flatMap RsaPublicPrecomputedAllMdHash.artifacts)

spec_apis artifacts

end VG.Artifacts.RsaPss.AArch64
