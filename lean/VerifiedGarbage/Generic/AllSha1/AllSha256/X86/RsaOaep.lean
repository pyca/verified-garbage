module

public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.X86.Inst

/-! # RSAES-OAEP encryption on x86 with the SHA-512 family, with MGF1's hash function as a table -/

@[expose] public section

namespace VG.Generic.AllSha1.AllSha256.X86.RsaOaep

open VG.Proof.RsaOaep.X86 (OK dec_ok enc_ok_sha1 enc_ok_sha224 enc_ok_sha256 enc_ok_sha384 enc_ok_sha512
  enc_ok_sha512_224 enc_ok_sha512_256)
open VG.Proof.HashTable.X86 (vars tables)

def artifacts (vs1 : List Proof.Sha1.X86.Variants.Backend) (vs256 : List Proof.Sha256.X86.Variants.Backend) : List Artifact :=
  if h : OK (vars vs1 vs256) then [
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha384).artifact X86.target {
      suffix := Emit.qualifiedName "" []
      tables := [("mgf1", tables (vars vs1 vs256))]
      code := Proof.RsaOaep.X86.Enc.encryptCode Proof.RsaOaep.X86.sha384 (vars vs1 vs256) Proof.RsaPkcs1Sig.X86.Ver.baseline
      stack := Proof.RsaOaep.X86.Enc.stackBytes
      verified := enc_ok_sha384 _ h
      spSafe := Proof.RsaOaep.X86.Enc.code_sp Proof.RsaPkcs1Sig.X86.Ver.baseline
      features := [] },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha512).artifact X86.target {
      suffix := Emit.qualifiedName "" []
      tables := [("mgf1", tables (vars vs1 vs256))]
      code := Proof.RsaOaep.X86.Enc.encryptCode Proof.RsaOaep.X86.sha512 (vars vs1 vs256) Proof.RsaPkcs1Sig.X86.Ver.baseline
      stack := Proof.RsaOaep.X86.Enc.stackBytes
      verified := enc_ok_sha512 _ h
      spSafe := Proof.RsaOaep.X86.Enc.code_sp Proof.RsaPkcs1Sig.X86.Ver.baseline
      features := [] },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha512_224).artifact X86.target {
      suffix := Emit.qualifiedName "" []
      tables := [("mgf1", tables (vars vs1 vs256))]
      code := Proof.RsaOaep.X86.Enc.encryptCode Proof.RsaOaep.X86.sha512_224 (vars vs1 vs256) Proof.RsaPkcs1Sig.X86.Ver.baseline
      stack := Proof.RsaOaep.X86.Enc.stackBytes
      verified := enc_ok_sha512_224 _ h
      spSafe := Proof.RsaOaep.X86.Enc.code_sp Proof.RsaPkcs1Sig.X86.Ver.baseline
      features := [] },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha512_256).artifact X86.target {
      suffix := Emit.qualifiedName "" []
      tables := [("mgf1", tables (vars vs1 vs256))]
      code := Proof.RsaOaep.X86.Enc.encryptCode Proof.RsaOaep.X86.sha512_256 (vars vs1 vs256) Proof.RsaPkcs1Sig.X86.Ver.baseline
      stack := Proof.RsaOaep.X86.Enc.stackBytes
      verified := enc_ok_sha512_256 _ h
      spSafe := Proof.RsaOaep.X86.Enc.code_sp Proof.RsaPkcs1Sig.X86.Ver.baseline
      features := [] }]
  else []

end VG.Generic.AllSha1.AllSha256.X86.RsaOaep
