module

public import VerifiedGarbage.Proof.RsaPss.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.AArch64
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.AArch64
public import VerifiedGarbage.Proof.Framework.QualifiedName

/-! # RSASSA-PSS (RFC 8017) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.RsaPss.AArch64.RsaPrivateCrtAllMdHash

open VG.Proof.MdHashTable.AArch64 (tables)
open VG.Proof.Variants.MdHash.AArch64 (variants hashes)

def artifacts (c : Proof.Rsa.AArch64.CrtImpl) : List Artifact := [
  Spec.RsaPss.signPrecomputedMdTableApi.artifact AArch64.target {
    suffix := qualifiedName "" [("crt", c.suffix)]
    tables := [("hash", tables variants), ("mgf1", tables variants)]
    code := Impl.RsaPss.AArch64.Fn.signCP hashes c.toCrt
    verified := .scrubbed (Proof.RsaPss.AArch64.Scrub.signCP_scrubbed c) }]

end VG.Artifacts.RsaPss.AArch64.RsaPrivateCrtAllMdHash

-- RSASSA-PSS verification on AArch64 with a precomputed key, with the hash functions as tables
namespace VG.Artifacts.RsaPss.AArch64.RsaPublicPrecomputedAllMdHash

open VG.Proof.MdHashTable.AArch64 (tables)
open VG.Proof.Variants.MdHash.AArch64 (variants hashes)

def artifacts (c : Proof.Rsa.AArch64.PublicImpl) : List Artifact := [
  Spec.RsaPss.verifyPrecomputedMdTableApi.artifact AArch64.target {
    suffix := qualifiedName "" [("rsa", c.suffix)]
    tables := [("hash", tables variants), ("mgf1", tables variants)]
    code := Impl.RsaPss.AArch64.Fn.verifyC hashes c.name c.code
    verified := .scrubbed (Proof.RsaPss.AArch64.Scrub.verifyC_scrubbed c) }]

end VG.Artifacts.RsaPss.AArch64.RsaPublicPrecomputedAllMdHash

namespace VG.Artifacts.RsaPss.AArch64

def artifacts : List Artifact :=
  (VG.Proof.Variants.RsaPrivateCrt.AArch64.variants.flatMap RsaPrivateCrtAllMdHash.artifacts) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.AArch64.variants.flatMap RsaPublicPrecomputedAllMdHash.artifacts)

end VG.Artifacts.RsaPss.AArch64
