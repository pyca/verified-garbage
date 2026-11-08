module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.X86.Inst
public import VerifiedGarbage.Spec.RsaOaep.Tables
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Variants.Sha256.X86
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.X86

/-! # RSAES-OAEP encryption with a precomputed public key on x86, with both hash functions as tables -/

@[expose] public section

namespace VG.Artifacts.RsaOaep.X86.AllSha1AllSha256

open VG.Proof.RsaOaep.X86 (OK enc_ok)
open VG.Proof.HashTable.X86 (vars tables)

def artifacts (vs1 : List Proof.Sha1.X86.Variants.Backend) (vs256 : List Proof.Sha256.X86.Variants.Backend) :
    List Artifact :=
  if h : OK (vars vs1 vs256) then [
    Spec.RsaOaep.encryptTablesApi.artifact X86.target {
      suffix := Emit.qualifiedName "" []
      tables := [("hash", tables (vars vs1 vs256)), ("mgf1", tables (vars vs1 vs256))]
      code := Proof.RsaOaep.X86.Enc.encryptCode (vars vs1 vs256) Proof.RsaPkcs1Sig.X86.Ver.baseline
      stack := Proof.RsaOaep.X86.Enc.stackBytes
      verified := enc_ok _ h
      spSafe := Proof.RsaOaep.X86.Enc.code_sp Proof.RsaPkcs1Sig.X86.Ver.baseline
      features := [] }]
  else []

end VG.Artifacts.RsaOaep.X86.AllSha1AllSha256

-- RSAES-OAEP decryption on x86, with both hash functions as tables
namespace VG.Artifacts.RsaOaep.X86.RsaPrivateCrtAllSha1AllSha256

open VG.Proof.RsaOaep.X86 (OK dec_ok)
open VG.Proof.HashTable.X86 (vars tables)

def artifacts (c : Proof.Rsa.X86.PrivChecked.CrtImpl) (vs1 : List Proof.Sha1.X86.Variants.Backend)
    (vs256 : List Proof.Sha256.X86.Variants.Backend) : List Artifact :=
  if h : OK (vars vs1 vs256) then [
    Spec.RsaOaep.decryptTablesApi.artifact X86.target {
      suffix := Emit.qualifiedName "" [("crt", c.suffix)]
      tables := [("hash", tables (vars vs1 vs256)), ("mgf1", tables (vars vs1 vs256))]
      code := Proof.RsaOaep.X86.Dec.decCode (vars vs1 vs256) c
      stack := Proof.RsaOaep.X86.Dec.stackBytes
      verified := dec_ok _ h c
      spSafe := Proof.RsaOaep.X86.Dec.code_sp c
      features := c.features }]
  else []

end VG.Artifacts.RsaOaep.X86.RsaPrivateCrtAllSha1AllSha256

namespace VG.Artifacts.RsaOaep.X86

def artifacts : List Artifact :=
  AllSha1AllSha256.artifacts VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants ++
  (VG.Proof.Variants.RsaPrivateCrt.X86.variants.flatMap fun v => RsaPrivateCrtAllSha1AllSha256.artifacts v VG.Proof.Variants.Sha1.X86.variants VG.Proof.Variants.Sha256.X86.variants)

end VG.Artifacts.RsaOaep.X86
