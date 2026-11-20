module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.X86.Scrub
public import VerifiedGarbage.Impl.RsaOaep.X86.Fn
public import VerifiedGarbage.Proof.RsaOaep.X86.Inst
public import VerifiedGarbage.Spec.RsaOaep.MdTables
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Variants.Sha256.X86
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86
public import VerifiedGarbage.Proof.Framework.QualifiedName

/-! # RSAES-OAEP (RFC 8017) on x86 -/

@[expose] public section

namespace VG.Artifacts.RsaOaep.X86.AllSha1AllSha256

open VG.Proof.RsaOaep.X86 (OK)
open VG.Proof.RsaOaep.X86.Scrub (allVars encrypt_scrubbed)
open VG.Proof.HashTable.X86 (tables fnsOf)

def artifacts : List Artifact :=
  if h : OK allVars then [
    Spec.RsaOaep.encryptMdTablesApi.artifact X86.target {
      suffix := qualifiedName "" []
      tables := [("hash", tables allVars), ("mgf1", tables allVars)]
      code := Impl.RsaOaep.X86.Fn.encryptPrecomputed (fnsOf allVars) Proof.RsaPkcs1Sig.X86.Ver.baseline.name
        Proof.RsaPkcs1Sig.X86.Ver.baseline.code
      verified := .scrubbed (encrypt_scrubbed h) }]
  else []

end VG.Artifacts.RsaOaep.X86.AllSha1AllSha256

-- RSAES-OAEP decryption on x86, with both hash functions as tables
namespace VG.Artifacts.RsaOaep.X86.RsaPrivateCrtAllSha1AllSha256

open VG.Proof.RsaOaep.X86 (OK)
open VG.Proof.HashTable.X86 (tables fnsOf)
open VG.Proof.RsaOaep.X86.Scrub (allVars decrypt_scrubbed decrypt_spSafe)
open VG.Proof.Rsa.X86.PrivChecked (crtPBaseline privCodeP)

def artifacts (c : Proof.Rsa.X86.PrivChecked.CrtImpl) : List Artifact :=
  if h : OK allVars then [
    Spec.RsaOaep.decryptPrecomputedMdTablesApi.artifact X86.target {
      suffix := qualifiedName "" [("crt", c.suffix)]
      tables := [("hash", tables allVars), ("mgf1", tables allVars)]
      code := Impl.RsaOaep.X86.Fn.decryptPrecomputed (fnsOf allVars) (Proof.RsaOaep.X86.Dec.privNameP c)
        (privCodeP c crtPBaseline)
      verified := .scrubbed (decrypt_scrubbed h c)
      spSafe := decrypt_spSafe c }]
  else []

end VG.Artifacts.RsaOaep.X86.RsaPrivateCrtAllSha1AllSha256

namespace VG.Artifacts.RsaOaep.X86

def artifacts : List Artifact :=
  AllSha1AllSha256.artifacts ++
  (VG.Proof.Variants.RsaPrivateCrt.X86.variants.flatMap fun v => RsaPrivateCrtAllSha1AllSha256.artifacts v)

end VG.Artifacts.RsaOaep.X86
