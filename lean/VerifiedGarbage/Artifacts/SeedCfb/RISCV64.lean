module

public import VerifiedGarbage.Proof.Seed.RISCV64.ModesVerified
public import VerifiedGarbage.Proof.Seed.RISCV64.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Seed.RISCV64.ModesLit
import VerifiedGarbage.Proof.Seed.RISCV64.FbFinalLit

/-! # SEED-CFB128 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.SeedCfb.RISCV64

def artifacts : List Artifact := [
  Spec.Seed.cfbEncryptApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.cfbEncrypt
    verified := Proof.Seed.RISCV64.Modes.cfbEncrypt_verified },
  Spec.Seed.cfbDecryptApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.cfbDecrypt
    verified := Proof.Seed.RISCV64.Modes.cfbDecrypt_verified },
  Spec.Seed.cfbEncryptFinalApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.cfbEncryptFinal
    verified := Proof.Seed.RISCV64.Modes.cfbEncryptFinal_verified },
  Spec.Seed.cfbDecryptFinalApi.artifact RISCV64.target {
    code := Impl.Seed.RISCV64.cfbDecryptFinal
    verified := Proof.Seed.RISCV64.Modes.cfbDecryptFinal_verified }]

end VG.Artifacts.SeedCfb.RISCV64
