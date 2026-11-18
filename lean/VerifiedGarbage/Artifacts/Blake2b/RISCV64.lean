module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Blake2.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Blake2.RISCV64.Lit
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Lit

/-! # BLAKE2b (RFC 7693) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Blake2b.RISCV64

def artifacts : List Artifact := [
  Spec.Blake2.initBApi.artifact RISCV64.target Proof.Blake2.RISCV64.initBReg,
  Spec.Blake2.updateBApi.artifact RISCV64.target Proof.Blake2.RISCV64.updateBReg,
  Spec.Blake2.finalizeBApi.artifact RISCV64.target Proof.Blake2.RISCV64.finalizeBReg]

end VG.Artifacts.Blake2b.RISCV64
