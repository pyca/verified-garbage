module

public import VerifiedGarbage.Proof.RsaPss.AArch64.Scrub
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaPss.AArch64.Sat
public import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Callees
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.AArch64
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.AArch64
public import VerifiedGarbage.Proof.Framework.QualifiedName

/-! # RSASSA-PSS (RFC 8017) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.RsaPss.AArch64.RsaPrivateCrtAllMdHash

open VG.Proof.RsaPkcs1Sig.AArch64 (privPOf)
open VG.Proof.RsaPss.AArch64 (signP_ok OK)

def artifacts (c : Proof.Rsa.AArch64.CrtImpl) (hc : c ∈ VG.Proof.Variants.RsaPrivateCrt.AArch64.variants) :
    List Artifact :=
  if h : OK VG.Proof.Variants.MdHash.AArch64.variants then [
    Spec.RsaPss.signPrecomputedMdTableApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := qualifiedName "" [("crt", c.suffix)]
      tables := [("hash", Proof.MdHashTable.AArch64.tables VG.Proof.Variants.MdHash.AArch64.variants), ("mgf1", Proof.MdHashTable.AArch64.tables VG.Proof.Variants.MdHash.AArch64.variants)]
      code := Impl.RsaPss.AArch64.signCP (Proof.MdHashTable.AArch64.fnsOf VG.Proof.Variants.MdHash.AArch64.variants) (Proof.HashTable.AArch64.fnsOf VG.Proof.Variants.MdHash.AArch64.variants)
        (privPOf c).name (privPOf c).code
      verified := signP_ok h c } Proof.RsaPss.AArch64.Scrub.clear (Proof.RsaPss.AArch64.Scrub.signOk _ _ _)
      (Proof.RsaPss.AArch64.Scrub.signSide c hc))]
  else []

end VG.Artifacts.RsaPss.AArch64.RsaPrivateCrtAllMdHash

-- RSASSA-PSS verification on AArch64 with a precomputed key, with the hash functions as tables
namespace VG.Artifacts.RsaPss.AArch64.RsaPublicPrecomputedAllMdHash

open VG.Proof.RsaPkcs1Sig.AArch64 (pdOf)
open VG.Proof.RsaPss.AArch64 (verify_ok OK)

def artifacts (c : Proof.Rsa.AArch64.PublicImpl)
    (hc : c ∈ VG.Proof.Variants.RsaPublicPrecomputed.AArch64.variants) : List Artifact :=
  if h : OK VG.Proof.Variants.MdHash.AArch64.variants then [
    Spec.RsaPss.verifyPrecomputedMdTableApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := qualifiedName "" [("rsa", c.suffix)]
      tables := [("hash", Proof.MdHashTable.AArch64.tables VG.Proof.Variants.MdHash.AArch64.variants), ("mgf1", Proof.MdHashTable.AArch64.tables VG.Proof.Variants.MdHash.AArch64.variants)]
      code := Impl.RsaPss.AArch64.verifyC (Proof.MdHashTable.AArch64.fnsOf VG.Proof.Variants.MdHash.AArch64.variants) (Proof.HashTable.AArch64.fnsOf VG.Proof.Variants.MdHash.AArch64.variants)
        (pdOf c).name (pdOf c).code
      verified := verify_ok h c } Proof.RsaPss.AArch64.Scrub.clear (Proof.RsaPss.AArch64.Scrub.verifyOk _ _ _)
      (Proof.RsaPss.AArch64.Scrub.verifySide c hc))]
  else []

end VG.Artifacts.RsaPss.AArch64.RsaPublicPrecomputedAllMdHash

namespace VG.Artifacts.RsaPss.AArch64

def artifacts : List Artifact :=
  (VG.Proof.Variants.RsaPrivateCrt.AArch64.variants.attach.flatMap fun v => RsaPrivateCrtAllMdHash.artifacts v.1 v.2) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.AArch64.variants.attach.flatMap fun v =>
    RsaPublicPrecomputedAllMdHash.artifacts v.1 v.2)

end VG.Artifacts.RsaPss.AArch64
