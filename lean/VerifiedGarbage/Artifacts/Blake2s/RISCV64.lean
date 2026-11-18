module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Blake2.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Blake2.RISCV64.Lit
import VerifiedGarbage.Proof.Blake2.RISCV64.Stream.Lit

/-! # BLAKE2s (RFC 7693) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Blake2s.RISCV64

def artifacts : List Artifact := [
  Spec.Blake2.initSApi.artifact RISCV64.target Proof.Blake2.RISCV64.initSReg,
  Spec.Blake2.updateSApi.artifact RISCV64.target Proof.Blake2.RISCV64.updateSReg,
  Spec.Blake2.finalizeSApi.artifact RISCV64.target Proof.Blake2.RISCV64.finalizeSReg]

end VG.Artifacts.Blake2s.RISCV64
