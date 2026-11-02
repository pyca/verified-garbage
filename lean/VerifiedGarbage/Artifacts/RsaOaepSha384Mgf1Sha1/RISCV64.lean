module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Verified
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSAES-OAEP with SHA-384 and MGF1 with SHA-1 on RISC-V: encryption and decryption -/

@[expose] public section

namespace VG.Artifacts.RsaOaepSha384Mgf1Sha1.RISCV64

def artifacts : List Artifact := [
  (Spec.RsaOaep.encryptPrecomputedApi Spec.Mgf1.sha384 Spec.Mgf1.sha1).artifact RISCV64.target {
    code := Impl.RsaOaep.RISCV64.encrypt
      Proof.Hmac.Stream.RISCV64.Sha384.hash Proof.Hmac.Stream.RISCV64.Sha1.hash
    stack := 336
    verified := Proof.RsaOaep.RISCV64.link_verified Proof.RsaOaep.RISCV64.sha384L Proof.RsaOaep.RISCV64.sha1L },
  (Spec.RsaOaep.decryptApi Spec.Mgf1.sha384 Spec.Mgf1.sha1).artifact RISCV64.target {
    code := Impl.RsaOaep.RISCV64.Dec.decrypt
      Proof.Hmac.Stream.RISCV64.Sha384.hash Proof.Hmac.Stream.RISCV64.Sha1.hash
    stack := 3472
    verified := Proof.RsaOaep.RISCV64.Dec.dec_link_verified Proof.RsaOaep.RISCV64.sha384L
      Proof.RsaOaep.RISCV64.sha1L }]

end VG.Artifacts.RsaOaepSha384Mgf1Sha1.RISCV64
