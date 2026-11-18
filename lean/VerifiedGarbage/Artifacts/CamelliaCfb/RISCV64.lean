module

public import VerifiedGarbage.Proof.Camellia.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit
import VerifiedGarbage.Proof.Camellia.RISCV64.FbFinalLit

/-! # Camellia-CFB128 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.RISCV64

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact RISCV64.target Proof.Camellia.RISCV64.Scrub.cfbEncryptReg,
  Spec.Camellia.cfbDecryptApi.artifact RISCV64.target Proof.Camellia.RISCV64.Scrub.cfbDecryptReg,
  Spec.Camellia.cfbEncryptFinalApi.artifact RISCV64.target Proof.Camellia.RISCV64.Scrub.cfbEncryptFinalReg,
  Spec.Camellia.cfbDecryptFinalApi.artifact RISCV64.target Proof.Camellia.RISCV64.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.CamelliaCfb.RISCV64
