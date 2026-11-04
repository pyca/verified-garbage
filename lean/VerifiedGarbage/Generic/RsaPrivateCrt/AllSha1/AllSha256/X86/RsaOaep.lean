module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.X86.Inst

/-! # RSAES-OAEP decryption on x86 with the SHA-512 family, with MGF1's hash function as a table -/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.AllSha1.AllSha256.X86.RsaOaep

open VG.Proof.RsaOaep.X86 (OK dec_ok enc_ok_sha1 enc_ok_sha224 enc_ok_sha256 enc_ok_sha384 enc_ok_sha512
  enc_ok_sha512_224 enc_ok_sha512_256)
open VG.Proof.HashTable.X86 (vars tables)

def artifacts (c : Proof.Rsa.X86.PrivChecked.CrtImpl) (vs1 : List Proof.Sha1.X86.Variants.Backend) (vs256 : List Proof.Sha256.X86.Variants.Backend) : List Artifact :=
  if h : OK (vars vs1 vs256) then [
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha384).artifact X86.target {
      suffix := Emit.qualifiedName "" [("crt", c.suffix)]
      tables := [("mgf1", tables (vars vs1 vs256))]
      code := Proof.RsaOaep.X86.Dec.decCode Proof.RsaOaep.X86.sha384 (vars vs1 vs256) c
      stack := Proof.RsaOaep.X86.Dec.stackBytes
      verified := dec_ok Proof.RsaOaep.X86.sha384 _ h c
      spSafe := Proof.RsaOaep.X86.Dec.code_sp c
      features := c.features },
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha512).artifact X86.target {
      suffix := Emit.qualifiedName "" [("crt", c.suffix)]
      tables := [("mgf1", tables (vars vs1 vs256))]
      code := Proof.RsaOaep.X86.Dec.decCode Proof.RsaOaep.X86.sha512 (vars vs1 vs256) c
      stack := Proof.RsaOaep.X86.Dec.stackBytes
      verified := dec_ok Proof.RsaOaep.X86.sha512 _ h c
      spSafe := Proof.RsaOaep.X86.Dec.code_sp c
      features := c.features },
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha512_224).artifact X86.target {
      suffix := Emit.qualifiedName "" [("crt", c.suffix)]
      tables := [("mgf1", tables (vars vs1 vs256))]
      code := Proof.RsaOaep.X86.Dec.decCode Proof.RsaOaep.X86.sha512_224 (vars vs1 vs256) c
      stack := Proof.RsaOaep.X86.Dec.stackBytes
      verified := dec_ok Proof.RsaOaep.X86.sha512_224 _ h c
      spSafe := Proof.RsaOaep.X86.Dec.code_sp c
      features := c.features },
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha512_256).artifact X86.target {
      suffix := Emit.qualifiedName "" [("crt", c.suffix)]
      tables := [("mgf1", tables (vars vs1 vs256))]
      code := Proof.RsaOaep.X86.Dec.decCode Proof.RsaOaep.X86.sha512_256 (vars vs1 vs256) c
      stack := Proof.RsaOaep.X86.Dec.stackBytes
      verified := dec_ok Proof.RsaOaep.X86.sha512_256 _ h c
      spSafe := Proof.RsaOaep.X86.Dec.code_sp c
      features := c.features }]
  else []

end VG.Generic.RsaPrivateCrt.AllSha1.AllSha256.X86.RsaOaep
