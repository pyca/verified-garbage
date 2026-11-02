module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Verified
public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Dc.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSAES-OAEP with SHA-512 and MGF1 with SHA-512 on RISC-V: encryption and decryption -/

@[expose] public section

namespace VG.Artifacts.RsaOaepSha512Mgf1Sha512.RISCV64

def artifacts : List Artifact := [
  (Spec.RsaOaep.encryptPrecomputedApi Spec.Mgf1.sha512 Spec.Mgf1.sha512).artifact RISCV64.target {
    code := Impl.RsaOaep.RISCV64.encrypt
      Proof.Hmac.Stream.RISCV64.Sha512.hash Proof.Hmac.Stream.RISCV64.Sha512.hash
    stack := 336
    verified := Proof.RsaOaep.RISCV64.link_verified Proof.RsaOaep.RISCV64.sha512L Proof.RsaOaep.RISCV64.sha512L },
  (Spec.RsaOaep.decryptApi Spec.Mgf1.sha512 Spec.Mgf1.sha512).artifact RISCV64.target {
    code := Impl.RsaOaep.RISCV64.Dec.decrypt
      Proof.Hmac.Stream.RISCV64.Sha512.hash Proof.Hmac.Stream.RISCV64.Sha512.hash
    stack := 3472
    verified := Proof.RsaOaep.RISCV64.Dec.dec_link_verified Proof.RsaOaep.RISCV64.sha512L
      Proof.RsaOaep.RISCV64.sha512L }]

end VG.Artifacts.RsaOaepSha512Mgf1Sha512.RISCV64
