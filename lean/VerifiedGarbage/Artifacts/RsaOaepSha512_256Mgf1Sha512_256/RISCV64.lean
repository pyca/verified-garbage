module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSAES-OAEP with SHA-512/256 and MGF1 with SHA-512/256 on RISC-V: encryption -/

@[expose] public section

namespace VG.Artifacts.RsaOaepSha512_256Mgf1Sha512_256.RISCV64

def artifacts : List Artifact := [
  (Spec.RsaOaep.encryptPrecomputedApi Spec.Mgf1.sha512_256 Spec.Mgf1.sha512_256).artifact RISCV64.target {
    code := Impl.RsaOaep.RISCV64.encrypt
      Proof.Hmac.Stream.RISCV64.Sha512_256.hash Proof.Hmac.Stream.RISCV64.Sha512_256.hash
    stack := 336
    verified := Proof.RsaOaep.RISCV64.link_verified Proof.RsaOaep.RISCV64.sha512_256L
      Proof.RsaOaep.RISCV64.sha512_256L }]

end VG.Artifacts.RsaOaepSha512_256Mgf1Sha512_256.RISCV64
