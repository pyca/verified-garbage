module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.X86.Inst
public import VerifiedGarbage.Spec.RsaOaep.Tables

/-! # RSAES-OAEP decryption on x86, with both hash functions as tables -/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.AllSha1.AllSha256.X86.RsaOaep

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

end VG.Generic.RsaPrivateCrt.AllSha1.AllSha256.X86.RsaOaep
