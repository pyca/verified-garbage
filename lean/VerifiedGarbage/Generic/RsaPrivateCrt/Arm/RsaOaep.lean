module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.Arm.Inst
public import VerifiedGarbage.Proof.Rsa.Arm.PublicOfCrt

/-! # RSAES-OAEP on ARMv7, with MGF1's hash function as a table -/

@[expose] public section

namespace VG.Generic.RsaPrivateCrt.Arm.RsaOaep

open VG.Proof.Rsa.Arm (CrtImpl)
open VG.Proof.RsaOaep.Arm (OK dec_ok enc_ok_sha1 enc_ok_sha224 enc_ok_sha256 enc_ok_sha384 enc_ok_sha512
  enc_ok_sha512_224 enc_ok_sha512_256)
open VG.Proof.HashTable.Arm (vars tables)

def artifacts (v : CrtImpl) : List Artifact :=
  if h : OK vars then [
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha1).artifact Arm.target {
      suffix := v.suffix
      tables := [("mgf1", tables vars)]
      code := Proof.RsaOaep.Arm.Dec.decCode (.ofPss Proof.RsaPss.Arm.sha1) vars v
      stack := 3624
      verified := dec_ok (.ofPss Proof.RsaPss.Arm.sha1) vars h v
      features := v.features },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha1).artifact Arm.target {
      suffix := v.suffix
      tables := [("mgf1", tables vars)]
      code := Proof.RsaOaep.Arm.Enc.encryptCode (.ofPss Proof.RsaPss.Arm.sha1) vars (Proof.Rsa.Arm.pdOfCrt v)
      stack := 240
      verified := enc_ok_sha1 vars h (Proof.Rsa.Arm.pdOfCrt v)
      features := v.features },
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha224).artifact Arm.target {
      suffix := v.suffix
      tables := [("mgf1", tables vars)]
      code := Proof.RsaOaep.Arm.Dec.decCode (.ofPss Proof.RsaPss.Arm.sha224) vars v
      stack := 3624
      verified := dec_ok (.ofPss Proof.RsaPss.Arm.sha224) vars h v
      features := v.features },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha224).artifact Arm.target {
      suffix := v.suffix
      tables := [("mgf1", tables vars)]
      code := Proof.RsaOaep.Arm.Enc.encryptCode (.ofPss Proof.RsaPss.Arm.sha224) vars (Proof.Rsa.Arm.pdOfCrt v)
      stack := 240
      verified := enc_ok_sha224 vars h (Proof.Rsa.Arm.pdOfCrt v)
      features := v.features },
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha256).artifact Arm.target {
      suffix := v.suffix
      tables := [("mgf1", tables vars)]
      code := Proof.RsaOaep.Arm.Dec.decCode (.ofPss Proof.RsaPss.Arm.sha256) vars v
      stack := 3624
      verified := dec_ok (.ofPss Proof.RsaPss.Arm.sha256) vars h v
      features := v.features },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha256).artifact Arm.target {
      suffix := v.suffix
      tables := [("mgf1", tables vars)]
      code := Proof.RsaOaep.Arm.Enc.encryptCode (.ofPss Proof.RsaPss.Arm.sha256) vars (Proof.Rsa.Arm.pdOfCrt v)
      stack := 240
      verified := enc_ok_sha256 vars h (Proof.Rsa.Arm.pdOfCrt v)
      features := v.features },
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha384).artifact Arm.target {
      suffix := v.suffix
      tables := [("mgf1", tables vars)]
      code := Proof.RsaOaep.Arm.Dec.decCode (.ofPss Proof.RsaPss.Arm.sha384) vars v
      stack := 3624
      verified := dec_ok (.ofPss Proof.RsaPss.Arm.sha384) vars h v
      features := v.features },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha384).artifact Arm.target {
      suffix := v.suffix
      tables := [("mgf1", tables vars)]
      code := Proof.RsaOaep.Arm.Enc.encryptCode (.ofPss Proof.RsaPss.Arm.sha384) vars (Proof.Rsa.Arm.pdOfCrt v)
      stack := 240
      verified := enc_ok_sha384 vars h (Proof.Rsa.Arm.pdOfCrt v)
      features := v.features },
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha512).artifact Arm.target {
      suffix := v.suffix
      tables := [("mgf1", tables vars)]
      code := Proof.RsaOaep.Arm.Dec.decCode (.ofPss Proof.RsaPss.Arm.sha512) vars v
      stack := 3624
      verified := dec_ok (.ofPss Proof.RsaPss.Arm.sha512) vars h v
      features := v.features },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha512).artifact Arm.target {
      suffix := v.suffix
      tables := [("mgf1", tables vars)]
      code := Proof.RsaOaep.Arm.Enc.encryptCode (.ofPss Proof.RsaPss.Arm.sha512) vars (Proof.Rsa.Arm.pdOfCrt v)
      stack := 240
      verified := enc_ok_sha512 vars h (Proof.Rsa.Arm.pdOfCrt v)
      features := v.features },
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha512_224).artifact Arm.target {
      suffix := v.suffix
      tables := [("mgf1", tables vars)]
      code := Proof.RsaOaep.Arm.Dec.decCode (.ofPss Proof.RsaPss.Arm.sha512_224) vars v
      stack := 3624
      verified := dec_ok (.ofPss Proof.RsaPss.Arm.sha512_224) vars h v
      features := v.features },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha512_224).artifact Arm.target {
      suffix := v.suffix
      tables := [("mgf1", tables vars)]
      code := Proof.RsaOaep.Arm.Enc.encryptCode (.ofPss Proof.RsaPss.Arm.sha512_224) vars (Proof.Rsa.Arm.pdOfCrt v)
      stack := 240
      verified := enc_ok_sha512_224 vars h (Proof.Rsa.Arm.pdOfCrt v)
      features := v.features },
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha512_256).artifact Arm.target {
      suffix := v.suffix
      tables := [("mgf1", tables vars)]
      code := Proof.RsaOaep.Arm.Dec.decCode (.ofPss Proof.RsaPss.Arm.sha512_256) vars v
      stack := 3624
      verified := dec_ok (.ofPss Proof.RsaPss.Arm.sha512_256) vars h v
      features := v.features },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha512_256).artifact Arm.target {
      suffix := v.suffix
      tables := [("mgf1", tables vars)]
      code := Proof.RsaOaep.Arm.Enc.encryptCode (.ofPss Proof.RsaPss.Arm.sha512_256) vars (Proof.Rsa.Arm.pdOfCrt v)
      stack := 240
      verified := enc_ok_sha512_256 vars h (Proof.Rsa.Arm.pdOfCrt v)
      features := v.features }]
  else []

end VG.Generic.RsaPrivateCrt.Arm.RsaOaep
