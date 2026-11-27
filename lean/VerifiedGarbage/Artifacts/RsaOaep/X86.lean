module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaOaep.MdTables
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.RsaOaep.X86.Scrub
import VerifiedGarbage.Impl.RsaOaep.X86.Fn
import VerifiedGarbage.Proof.RsaOaep.X86.Inst
import VerifiedGarbage.Proof.Variants.Sha1.X86
import VerifiedGarbage.Proof.Variants.Sha256.X86
import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86
import VerifiedGarbage.Proof.Framework.QualifiedName
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSAES-OAEP (RFC 8017) on x86 -/

namespace VG.Artifacts.RsaOaep.X86.AllSha1AllSha256

open VG.Proof.RsaOaep.X86 (OK)
open VG.Proof.RsaOaep.X86.Scrub (allVars encrypt_scrubbed)
open VG.Proof.HashTable.X86 (tables fnsOf)

def artifacts : List (Artifact X86.target) :=
  if h : OK allVars then [
    Spec.RsaOaep.encryptMdTablesApi.artifact X86.target {
      suffix := qualifiedName "" []
      tables := [("hash", tables allVars), ("mgf1", tables allVars)]
      code := Impl.RsaOaep.X86.Fn.encryptPrecomputed (fnsOf allVars) Proof.RsaPkcs1Sig.X86.Ver.baseline.name
        Proof.RsaPkcs1Sig.X86.Ver.baseline.code
      verified := Proof.RsaOaep.X86.Scrub.encrypt_scrubbed h }]
  else []

end VG.Artifacts.RsaOaep.X86.AllSha1AllSha256

-- RSAES-OAEP decryption on x86, with both hash functions as tables
namespace VG.Artifacts.RsaOaep.X86.RsaPrivateCrtAllSha1AllSha256

open VG.Proof.RsaOaep.X86 (OK)
open VG.Proof.HashTable.X86 (tables fnsOf)
open VG.Proof.RsaOaep.X86.Scrub (allVars decrypt_scrubbed decrypt_spSafe)
open VG.Proof.Rsa.X86.PrivChecked (crtPBaseline privCodeP)

def artifacts (c : Proof.Rsa.X86.PrivChecked.CrtImpl) : List (Artifact X86.target) :=
  if h : OK allVars then [
    Spec.RsaOaep.decryptPrecomputedMdTablesApi.artifact X86.target {
      suffix := qualifiedName "" [("crt", c.suffix)]
      tables := [("hash", tables allVars), ("mgf1", tables allVars)]
      code := Impl.RsaOaep.X86.Fn.decryptPrecomputed (fnsOf allVars) (Proof.RsaOaep.X86.Dec.privNameP c)
        (privCodeP c crtPBaseline)
      verified := Proof.RsaOaep.X86.Scrub.decrypt_scrubbed h c
      spSafe := Proof.RsaOaep.X86.Scrub.decrypt_spSafe c }]
  else []

end VG.Artifacts.RsaOaep.X86.RsaPrivateCrtAllSha1AllSha256

namespace VG.Artifacts.RsaOaep.X86

public def artifacts : List (Artifact X86.target) :=
  AllSha1AllSha256.artifacts ++
  (VG.Proof.Variants.RsaPrivateCrt.X86.variants.flatMap fun v => RsaPrivateCrtAllSha1AllSha256.artifacts v)

spec_apis artifacts

end VG.Artifacts.RsaOaep.X86
