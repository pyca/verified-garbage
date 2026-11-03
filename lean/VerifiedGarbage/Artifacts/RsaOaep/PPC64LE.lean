module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.PPC64LE.Inst

/-! # RSAES-OAEP on PPC64LE, with MGF1's hash function as a table -/

@[expose] public section

namespace VG.Artifacts.RsaOaep.PPC64LE

open VG.Proof.RsaOaep.PPC64LE (OK enc_ok dec_ok sha1L sha224L sha256L sha384L sha512L sha512_224L sha512_256L)
open VG.Proof.HashTable.PPC64LE (vars tables fnsOf)

def artifacts : List Artifact :=
  if h : OK vars then [
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha1).artifact PPC64LE.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.PPC64LE.Dec.decrypt Proof.Hmac.Stream.PPC64LE.Sha1.hash (fnsOf vars)
      stack := 3776
      verified := dec_ok sha1L vars h },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha1).artifact PPC64LE.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.PPC64LE.encrypt Proof.Hmac.Stream.PPC64LE.Sha1.hash (fnsOf vars)
      stack := 304
      verified := enc_ok sha1L vars h },
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha224).artifact PPC64LE.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.PPC64LE.Dec.decrypt Proof.Hmac.Stream.PPC64LE.Sha224.hash (fnsOf vars)
      stack := 3776
      verified := dec_ok sha224L vars h },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha224).artifact PPC64LE.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.PPC64LE.encrypt Proof.Hmac.Stream.PPC64LE.Sha224.hash (fnsOf vars)
      stack := 304
      verified := enc_ok sha224L vars h },
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha256).artifact PPC64LE.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.PPC64LE.Dec.decrypt Proof.Hmac.Stream.PPC64LE.Sha256.hash (fnsOf vars)
      stack := 3776
      verified := dec_ok sha256L vars h },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha256).artifact PPC64LE.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.PPC64LE.encrypt Proof.Hmac.Stream.PPC64LE.Sha256.hash (fnsOf vars)
      stack := 304
      verified := enc_ok sha256L vars h },
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha384).artifact PPC64LE.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.PPC64LE.Dec.decrypt Proof.Hmac.Stream.PPC64LE.Sha384.hash (fnsOf vars)
      stack := 3776
      verified := dec_ok sha384L vars h },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha384).artifact PPC64LE.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.PPC64LE.encrypt Proof.Hmac.Stream.PPC64LE.Sha384.hash (fnsOf vars)
      stack := 304
      verified := enc_ok sha384L vars h },
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha512).artifact PPC64LE.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.PPC64LE.Dec.decrypt Proof.Hmac.Stream.PPC64LE.Sha512.hash (fnsOf vars)
      stack := 3776
      verified := dec_ok sha512L vars h },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha512).artifact PPC64LE.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.PPC64LE.encrypt Proof.Hmac.Stream.PPC64LE.Sha512.hash (fnsOf vars)
      stack := 304
      verified := enc_ok sha512L vars h },
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha512_224).artifact PPC64LE.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.PPC64LE.Dec.decrypt Proof.Hmac.Stream.PPC64LE.Sha512_224.hash (fnsOf vars)
      stack := 3776
      verified := dec_ok sha512_224L vars h },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha512_224).artifact PPC64LE.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.PPC64LE.encrypt Proof.Hmac.Stream.PPC64LE.Sha512_224.hash (fnsOf vars)
      stack := 304
      verified := enc_ok sha512_224L vars h },
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha512_256).artifact PPC64LE.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.PPC64LE.Dec.decrypt Proof.Hmac.Stream.PPC64LE.Sha512_256.hash (fnsOf vars)
      stack := 3776
      verified := dec_ok sha512_256L vars h },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha512_256).artifact PPC64LE.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.PPC64LE.encrypt Proof.Hmac.Stream.PPC64LE.Sha512_256.hash (fnsOf vars)
      stack := 304
      verified := enc_ok sha512_256L vars h }]
  else []

end VG.Artifacts.RsaOaep.PPC64LE
