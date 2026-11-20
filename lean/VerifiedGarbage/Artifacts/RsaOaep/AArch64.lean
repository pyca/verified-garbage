module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.AArch64
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.AArch64
public import VerifiedGarbage.Proof.Framework.QualifiedName

/-! # RSAES-OAEP (RFC 8017) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.RsaOaep.AArch64.RsaPrivateCrtAllMdHash

open VG.Proof.MdHashTable.AArch64 (tables)
open VG.Proof.Variants.MdHash.AArch64 (variants hashes)

def artifacts (c : Proof.Rsa.AArch64.CrtImpl) : List Artifact := [
  Spec.RsaOaep.decryptPrecomputedMdTablesApi.artifact AArch64.target {
    suffix := qualifiedName "" [("crt", c.suffix)]
    tables := [("hash", tables variants), ("mgf1", tables variants)]
    code := Impl.RsaOaep.AArch64.Fn.decryptP hashes c.toCrt
    verified := .scrubbed (Proof.RsaOaep.AArch64.Scrub.decryptP_scrubbed c) }]

end VG.Artifacts.RsaOaep.AArch64.RsaPrivateCrtAllMdHash

-- RSAES-OAEP encryption with a precomputed public key on AArch64, with both hash functions as tables
namespace VG.Artifacts.RsaOaep.AArch64.RsaPublicPrecomputedAllMdHash

open VG.Proof.MdHashTable.AArch64 (tables)
open VG.Proof.Variants.MdHash.AArch64 (variants hashes)

def artifacts (c : Proof.Rsa.AArch64.PublicImpl) : List Artifact := [
  Spec.RsaOaep.encryptMdTablesApi.artifact AArch64.target {
    suffix := qualifiedName "" [("rsa", c.suffix)]
    tables := [("hash", tables variants), ("mgf1", tables variants)]
    code := Impl.RsaOaep.AArch64.Fn.encrypt hashes c.name c.code
    verified := .scrubbed (Proof.RsaOaep.AArch64.Scrub.encrypt_scrubbed c) }]

end VG.Artifacts.RsaOaep.AArch64.RsaPublicPrecomputedAllMdHash

namespace VG.Artifacts.RsaOaep.AArch64

def artifacts : List Artifact :=
  (VG.Proof.Variants.RsaPrivateCrt.AArch64.variants.flatMap RsaPrivateCrtAllMdHash.artifacts) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.AArch64.variants.flatMap RsaPublicPrecomputedAllMdHash.artifacts)

end VG.Artifacts.RsaOaep.AArch64
