module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Verified
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSAES-OAEP with SHA-224 and MGF1 with SHA-224 on RISC-V: encryption and decryption -/

@[expose] public section

namespace VG.Artifacts.RsaOaepSha224Mgf1Sha224.RISCV64

def artifacts : List Artifact := [
  (Spec.RsaOaep.encryptPrecomputedApi Spec.Mgf1.sha224 Spec.Mgf1.sha224).artifact RISCV64.target {
    code := Impl.RsaOaep.RISCV64.encrypt
      Proof.Hmac.Stream.RISCV64.Sha256Family.hash224 Proof.Hmac.Stream.RISCV64.Sha256Family.hash224
    stack := 336
    verified := Proof.RsaOaep.RISCV64.link_verified Proof.RsaOaep.RISCV64.sha224L Proof.RsaOaep.RISCV64.sha224L },
  (Spec.RsaOaep.decryptApi Spec.Mgf1.sha224 Spec.Mgf1.sha224).artifact RISCV64.target {
    code := Impl.RsaOaep.RISCV64.Dec.decrypt
      Proof.Hmac.Stream.RISCV64.Sha256Family.hash224 Proof.Hmac.Stream.RISCV64.Sha256Family.hash224
    stack := 3472
    verified := Proof.RsaOaep.RISCV64.Dec.dec_link_verified Proof.RsaOaep.RISCV64.sha224L
      Proof.RsaOaep.RISCV64.sha224L }]

end VG.Artifacts.RsaOaepSha224Mgf1Sha224.RISCV64
