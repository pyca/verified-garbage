module

public import VerifiedGarbage.Proof.Poly1305.RISCV64.Scrub
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Poly1305.RISCV64.Lit

/-! # Poly1305 (RFC 8439 §2.5) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Poly1305.RISCV64

def artifacts : List Artifact := [
  Spec.Poly1305.initApi.artifact RISCV64.target Proof.Poly1305.RISCV64.Scrub.initReg,
  Spec.Poly1305.updateApi.artifact RISCV64.target Proof.Poly1305.RISCV64.Scrub.updateReg,
  Spec.Poly1305.finalizeApi.artifact RISCV64.target Proof.Poly1305.RISCV64.Scrub.finalizeReg]

end VG.Artifacts.Poly1305.RISCV64
