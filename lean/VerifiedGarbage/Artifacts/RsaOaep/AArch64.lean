module

public import VerifiedGarbage.Proof.RsaOaep.AArch64.Scrub
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Inst
public import VerifiedGarbage.Spec.RsaOaep.MdTables
public import VerifiedGarbage.Proof.HashTable.AArch64
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.AArch64.TaintErase
public import VerifiedGarbage.Proof.Mgf1.Bytes
public import VerifiedGarbage.Proof.RsaOaep.AArch64.Args
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCT1
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCT2
public import VerifiedGarbage.Proof.RsaOaep.AArch64.DecCorrect
public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCT1
public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncCorrect
public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncEm
public import VerifiedGarbage.Proof.RsaOaep.AArch64.EncMain
public import VerifiedGarbage.Proof.RsaOaep.AArch64.LabelTCT
public import VerifiedGarbage.Proof.RsaOaep.AArch64.MgfCT
public import VerifiedGarbage.Proof.RsaOaep.AArch64.TaintImm
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.AArch64
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
public import VerifiedGarbage.Proof.Variants.RsaPublicPrecomputed.AArch64
public import VerifiedGarbage.Proof.Framework.QualifiedName

/-! # RSAES-OAEP (RFC 8017) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.RsaOaep.AArch64.RsaPrivateCrtAllMdHash

open VG.Proof.RsaOaep.AArch64 (decP_ok OK)
open VG.Proof.RsaPkcs1Sig.AArch64 (privPOf)
open VG.Proof.MdHashTable.AArch64 (tables)
open VG.Proof.HashTable.AArch64 (fnsOf)

def artifacts (c : Proof.Rsa.AArch64.CrtImpl) (hc : c ∈ VG.Proof.Variants.RsaPrivateCrt.AArch64.variants) :
    List Artifact :=
  if h : OK VG.Proof.Variants.MdHash.AArch64.variants then [
    Spec.RsaOaep.decryptPrecomputedMdTablesApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := qualifiedName "" [("crt", c.suffix)]
      tables := [("hash", tables VG.Proof.Variants.MdHash.AArch64.variants), ("mgf1", tables VG.Proof.Variants.MdHash.AArch64.variants)]
      code := Impl.RsaOaep.AArch64.decryptP (fnsOf VG.Proof.Variants.MdHash.AArch64.variants) (privPOf c).name (privPOf c).code
      verified := decP_ok VG.Proof.Variants.MdHash.AArch64.variants h c }
      Proof.RsaOaep.AArch64.Scrub.clear (Proof.RsaOaep.AArch64.Scrub.decryptOk VG.Proof.Variants.MdHash.AArch64.variants _)
      (Proof.RsaOaep.AArch64.Scrub.decryptSide c hc))]
  else []

end VG.Artifacts.RsaOaep.AArch64.RsaPrivateCrtAllMdHash

-- RSAES-OAEP encryption with a precomputed public key on AArch64, with both hash functions as tables
namespace VG.Artifacts.RsaOaep.AArch64.RsaPublicPrecomputedAllMdHash

open VG.Proof.RsaOaep.AArch64 (enc_ok OK)
open VG.Proof.RsaPkcs1Sig.AArch64 (pdOf)
open VG.Proof.MdHashTable.AArch64 (tables)
open VG.Proof.HashTable.AArch64 (fnsOf)

def artifacts (c : Proof.Rsa.AArch64.PublicImpl)
    (hc : c ∈ VG.Proof.Variants.RsaPublicPrecomputed.AArch64.variants) : List Artifact :=
  if h : OK VG.Proof.Variants.MdHash.AArch64.variants then [
    Spec.RsaOaep.encryptMdTablesApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := qualifiedName "" [("rsa", c.suffix)]
      tables := [("hash", tables VG.Proof.Variants.MdHash.AArch64.variants), ("mgf1", tables VG.Proof.Variants.MdHash.AArch64.variants)]
      code := Impl.RsaOaep.AArch64.Precomputed.encrypt (fnsOf VG.Proof.Variants.MdHash.AArch64.variants) (pdOf c).name (pdOf c).code
      verified := enc_ok VG.Proof.Variants.MdHash.AArch64.variants h c }
      Proof.RsaOaep.AArch64.Scrub.clear (Proof.RsaOaep.AArch64.Scrub.encryptOk VG.Proof.Variants.MdHash.AArch64.variants _)
      (Proof.RsaOaep.AArch64.Scrub.encryptSide c hc))]
  else []

end VG.Artifacts.RsaOaep.AArch64.RsaPublicPrecomputedAllMdHash

namespace VG.Artifacts.RsaOaep.AArch64

def artifacts : List Artifact :=
  (VG.Proof.Variants.RsaPrivateCrt.AArch64.variants.attach.flatMap fun v => RsaPrivateCrtAllMdHash.artifacts v.1 v.2) ++
  (VG.Proof.Variants.RsaPublicPrecomputed.AArch64.variants.attach.flatMap fun v =>
    RsaPublicPrecomputedAllMdHash.artifacts v.1 v.2)

end VG.Artifacts.RsaOaep.AArch64
