module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit
import VerifiedGarbage.Proof.TripleDes.RISCV64.FbFinalLit

/-! # Triple DES-OFB on RISC-V -/

@[expose] public section

namespace VG.Artifacts.TripleDesOfb.RISCV64

def artifacts : List Artifact := [
  Spec.TripleDes.ofbApi.artifact RISCV64.target Proof.TripleDes.RISCV64.Scrub.ofbReg,
  Spec.TripleDes.ofbFinalApi.artifact RISCV64.target Proof.TripleDes.RISCV64.Scrub.ofbFinalReg]

end VG.Artifacts.TripleDesOfb.RISCV64
