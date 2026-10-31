module

public import VerifiedGarbage.Proof.AesCtr.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesCtr.RISCV64.Lit

/-! # AES-CTR (NIST SP 800-38A §6.5) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesCtr.RISCV64

def artifacts : List Artifact := [
  Spec.Ctr.aesApi.artifact RISCV64.target {
    code := Impl.AesCtr.RISCV64.crypt
    verified := Proof.AesCtr.RISCV64.crypt_verified }]

end VG.Artifacts.AesCtr.RISCV64
