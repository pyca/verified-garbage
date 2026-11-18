module

public import VerifiedGarbage.Proof.Cast5.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Cast5.RISCV64.ModesLit
import VerifiedGarbage.Proof.Cast5.RISCV64.FbFinalLit

/-! # CAST5-OFB on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Cast5Ofb.RISCV64

def artifacts : List Artifact := [
  Spec.Cast5.ofbApi.artifact RISCV64.target Proof.Cast5.RISCV64.Scrub.ofbReg,
  Spec.Cast5.ofbFinalApi.artifact RISCV64.target Proof.Cast5.RISCV64.Scrub.ofbFinalReg]

end VG.Artifacts.Cast5Ofb.RISCV64
