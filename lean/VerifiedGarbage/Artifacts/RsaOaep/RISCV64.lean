module

public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Inst

/-! # RSAES-OAEP on RISC-V, with MGF1's hash function as a table -/

@[expose] public section

namespace VG.Artifacts.RsaOaep.RISCV64

open VG.Proof.RsaOaep.RISCV64 (OK enc_ok dec_ok sha1L sha224L sha256L sha384L sha512L sha512_224L sha512_256L)
open VG.Proof.HashTable.RISCV64 (vars tables fnsOf)

def artifacts : List Artifact :=
  if h : OK vars then [
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha1).artifact RISCV64.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.RISCV64.Dec.decrypt Proof.Hmac.Stream.RISCV64.Sha1.hash (fnsOf vars)
      stack := 3472
      verified := dec_ok sha1L vars h },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha1).artifact RISCV64.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.RISCV64.encrypt Proof.Hmac.Stream.RISCV64.Sha1.hash (fnsOf vars)
      stack := 336
      verified := enc_ok sha1L vars h },
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha224).artifact RISCV64.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.RISCV64.Dec.decrypt Proof.Hmac.Stream.RISCV64.Sha256Family.hash224 (fnsOf vars)
      stack := 3472
      verified := dec_ok sha224L vars h },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha224).artifact RISCV64.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.RISCV64.encrypt Proof.Hmac.Stream.RISCV64.Sha256Family.hash224 (fnsOf vars)
      stack := 336
      verified := enc_ok sha224L vars h },
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha256).artifact RISCV64.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.RISCV64.Dec.decrypt Proof.Hmac.Stream.RISCV64.Sha256Family.hash256 (fnsOf vars)
      stack := 3472
      verified := dec_ok sha256L vars h },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha256).artifact RISCV64.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.RISCV64.encrypt Proof.Hmac.Stream.RISCV64.Sha256Family.hash256 (fnsOf vars)
      stack := 336
      verified := enc_ok sha256L vars h },
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha384).artifact RISCV64.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.RISCV64.Dec.decrypt Proof.Hmac.Stream.RISCV64.Sha384.hash (fnsOf vars)
      stack := 3472
      verified := dec_ok sha384L vars h },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha384).artifact RISCV64.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.RISCV64.encrypt Proof.Hmac.Stream.RISCV64.Sha384.hash (fnsOf vars)
      stack := 336
      verified := enc_ok sha384L vars h },
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha512).artifact RISCV64.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.RISCV64.Dec.decrypt Proof.Hmac.Stream.RISCV64.Sha512.hash (fnsOf vars)
      stack := 3472
      verified := dec_ok sha512L vars h },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha512).artifact RISCV64.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.RISCV64.encrypt Proof.Hmac.Stream.RISCV64.Sha512.hash (fnsOf vars)
      stack := 336
      verified := enc_ok sha512L vars h },
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha512_224).artifact RISCV64.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.RISCV64.Dec.decrypt Proof.Hmac.Stream.RISCV64.Sha512_224.hash (fnsOf vars)
      stack := 3472
      verified := dec_ok sha512_224L vars h },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha512_224).artifact RISCV64.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.RISCV64.encrypt Proof.Hmac.Stream.RISCV64.Sha512_224.hash (fnsOf vars)
      stack := 336
      verified := enc_ok sha512_224L vars h },
    (Spec.RsaOaep.decryptTableApi Spec.Mgf1.sha512_256).artifact RISCV64.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.RISCV64.Dec.decrypt Proof.Hmac.Stream.RISCV64.Sha512_256.hash (fnsOf vars)
      stack := 3472
      verified := dec_ok sha512_256L vars h },
    (Spec.RsaOaep.encryptTableApi Spec.Mgf1.sha512_256).artifact RISCV64.target {
      tables := [("mgf1", tables vars)]
      code := Impl.RsaOaep.RISCV64.encrypt Proof.Hmac.Stream.RISCV64.Sha512_256.hash (fnsOf vars)
      stack := 336
      verified := enc_ok sha512_256L vars h }]
  else []

end VG.Artifacts.RsaOaep.RISCV64
