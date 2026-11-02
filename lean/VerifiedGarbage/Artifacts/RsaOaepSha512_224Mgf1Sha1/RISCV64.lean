module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSAES-OAEP with SHA-512/224 and MGF1 with SHA-1 on RISC-V: encryption -/

@[expose] public section

namespace VG.Artifacts.RsaOaepSha512_224Mgf1Sha1.RISCV64

def artifacts : List Artifact := [
  (Spec.RsaOaep.encryptPrecomputedApi Spec.Mgf1.sha512_224 Spec.Mgf1.sha1).artifact RISCV64.target {
    code := Impl.RsaOaep.RISCV64.encrypt
      Proof.Hmac.Stream.RISCV64.Sha512_224.hash Proof.Hmac.Stream.RISCV64.Sha1.hash
    stack := 336
    verified := Proof.RsaOaep.RISCV64.link_verified Proof.RsaOaep.RISCV64.sha512_224L Proof.RsaOaep.RISCV64.sha1L }]

end VG.Artifacts.RsaOaepSha512_224Mgf1Sha1.RISCV64
