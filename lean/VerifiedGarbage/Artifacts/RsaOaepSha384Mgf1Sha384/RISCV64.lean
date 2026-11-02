module

public import VerifiedGarbage.Proof.RsaOaep.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSAES-OAEP with SHA-384 and MGF1 with SHA-384 on RISC-V: encryption -/

@[expose] public section

namespace VG.Artifacts.RsaOaepSha384Mgf1Sha384.RISCV64

def artifacts : List Artifact := [
  (Spec.RsaOaep.encryptPrecomputedApi Spec.Mgf1.sha384 Spec.Mgf1.sha384).artifact RISCV64.target {
    code := Impl.RsaOaep.RISCV64.encrypt
      Proof.Hmac.Stream.RISCV64.Sha384.hash Proof.Hmac.Stream.RISCV64.Sha384.hash
    stack := 336
    verified := Proof.RsaOaep.RISCV64.link_verified Proof.RsaOaep.RISCV64.sha384L Proof.RsaOaep.RISCV64.sha384L }]

end VG.Artifacts.RsaOaepSha384Mgf1Sha384.RISCV64
