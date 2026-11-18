module

public import VerifiedGarbage.Proof.Camellia.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Camellia.RISCV64.Lit

/-! # Camellia on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Camellia.RISCV64

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact RISCV64.target Proof.Camellia.RISCV64.Scrub.expandKeyReg,
  Spec.Camellia.ecbEncryptApi.artifact RISCV64.target Proof.Camellia.RISCV64.Scrub.ecbEncryptReg,
  Spec.Camellia.ecbDecryptApi.artifact RISCV64.target Proof.Camellia.RISCV64.Scrub.ecbDecryptReg]

end VG.Artifacts.Camellia.RISCV64
