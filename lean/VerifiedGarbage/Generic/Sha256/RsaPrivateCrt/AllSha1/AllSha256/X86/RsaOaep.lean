module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.X86.Inst

/-! # RSAES-OAEP decryption on x86 with SHA-224 and SHA-256, with MGF1's hash function as a table -/

@[expose] public section

namespace VG.Generic.Sha256.RsaPrivateCrt.AllSha1.AllSha256.X86.RsaOaep

open VG.Proof.RsaOaep.X86 (OK dec_ok enc_ok_sha1 enc_ok_sha224 enc_ok_sha256 enc_ok_sha384 enc_ok_sha512
  enc_ok_sha512_224 enc_ok_sha512_256)
open VG.Proof.HashTable.X86 (vars tables)

def artifacts (v : Proof.Sha256.X86.Variants.Backend) (c : Proof.Rsa.X86.PrivChecked.CrtImpl)
    (vs1 : List Proof.Sha1.X86.Variants.Backend) (vs256 : List Proof.Sha256.X86.Variants.Backend) : List Artifact :=
  if h : OK (vars vs1 vs256) then [
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha224).artifact X86.target {
      suffix := Emit.qualifiedName "" [("sha256", v.stream.suffix), ("crt", c.suffix)]
      tables := [("mgf1", tables (vars vs1 vs256))]
      code := Proof.RsaOaep.X86.Dec.decCode (Proof.RsaOaep.X86.sha224 v) (vars vs1 vs256) c
      stack := Proof.RsaOaep.X86.Dec.stackBytes
      verified := dec_ok (Proof.RsaOaep.X86.sha224 v) _ h c
      spSafe := Proof.RsaOaep.X86.Dec.code_sp c
      features := v.features ++ c.features.filter (!v.features.contains ·) },
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha256).artifact X86.target {
      suffix := Emit.qualifiedName "" [("sha256", v.stream.suffix), ("crt", c.suffix)]
      tables := [("mgf1", tables (vars vs1 vs256))]
      code := Proof.RsaOaep.X86.Dec.decCode (Proof.RsaOaep.X86.sha256 v) (vars vs1 vs256) c
      stack := Proof.RsaOaep.X86.Dec.stackBytes
      verified := dec_ok (Proof.RsaOaep.X86.sha256 v) _ h c
      spSafe := Proof.RsaOaep.X86.Dec.code_sp c
      features := v.features ++ c.features.filter (!v.features.contains ·) }]
  else []

end VG.Generic.Sha256.RsaPrivateCrt.AllSha1.AllSha256.X86.RsaOaep
