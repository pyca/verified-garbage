module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaOaep.MdTables
import VerifiedGarbage.Proof.RsaOaep.AArch64.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.AArch64
import VerifiedGarbage.Proof.Variants.MdHash.AArch64
import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.AArch64
import VerifiedGarbage.Proof.Framework.QualifiedName
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSAES-OAEP (RFC 8017) on AArch64 -/

namespace VG.Artifacts.RsaOaep.AArch64.RsaPrivateCrtAllMdHash

open VG.Proof.MdHashTable.AArch64 (tables)
open VG.Proof.Variants.MdHash.AArch64 (variants hashes)

def artifacts (c : Proof.Rsa.AArch64.CrtImpl) : List (Artifact AArch64.target) := [
  Spec.RsaOaep.decryptPrecomputedMdTablesApi.artifact AArch64.target {
    suffix := qualifiedName "" [("crt", c.suffix)]
    tables := [("hash", tables variants), ("mgf1", tables variants)]
    code := Impl.RsaOaep.AArch64.Fn.decryptP hashes c.toCrt
    verified := Proof.RsaOaep.AArch64.Scrub.decryptP_scrubbed c }]

end VG.Artifacts.RsaOaep.AArch64.RsaPrivateCrtAllMdHash

-- RSAES-OAEP encryption with a precomputed public key on AArch64, with both hash functions as tables
namespace VG.Artifacts.RsaOaep.AArch64.RsaPublicPrecomputedAllMdHash

open VG.Proof.MdHashTable.AArch64 (tables)
open VG.Proof.Variants.MdHash.AArch64 (variants hashes)

def artifacts (c : Proof.Rsa.AArch64.PublicImpl) : List (Artifact AArch64.target) := [
  Spec.RsaOaep.encryptMdTablesApi.artifact AArch64.target {
    suffix := qualifiedName "" [("rsa", c.suffix)]
    tables := [("hash", tables variants), ("mgf1", tables variants)]
    code := Impl.RsaOaep.AArch64.Fn.encrypt hashes c.name c.code
    verified := Proof.RsaOaep.AArch64.Scrub.encrypt_scrubbed c }]

end VG.Artifacts.RsaOaep.AArch64.RsaPublicPrecomputedAllMdHash

namespace VG.Artifacts.RsaOaep.AArch64

public def artifacts : List (Artifact AArch64.target) :=
  (VG.Proof.Variants.RsaPrivateCrt.AArch64.variants.flatMap RsaPrivateCrtAllMdHash.artifacts) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.AArch64.variants.flatMap RsaPublicPrecomputedAllMdHash.artifacts)

spec_apis artifacts

end VG.Artifacts.RsaOaep.AArch64
