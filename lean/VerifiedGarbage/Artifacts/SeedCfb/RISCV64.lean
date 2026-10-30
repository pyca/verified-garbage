module

public import VerifiedGarbage.Proof.Seed.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.RISCV64.ModesLit

/-! # SEED-CFB128 artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.SeedCfb.RISCV64

def artifacts : List Artifact := [
  Spec.Seed.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.cfbEncrypt
    stack := 1104
    verified := Proof.Seed.RISCV64.Modes.cfbEncrypt_verified },
  Spec.Seed.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.cfbDecrypt
    stack := 1104
    verified := Proof.Seed.RISCV64.Modes.cfbDecrypt_verified }]

end VG.Artifacts.SeedCfb.RISCV64
