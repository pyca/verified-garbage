module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.X86.Inst
public import VerifiedGarbage.Spec.RsaOaep.Tables

/-! # RSAES-OAEP encryption with a precomputed public key on x86, with both hash functions as tables -/

@[expose] public section

namespace VG.Generic.AllSha1.AllSha256.X86.RsaOaep

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

end VG.Generic.AllSha1.AllSha256.X86.RsaOaep
