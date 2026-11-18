module

public import VerifiedGarbage.Proof.Camellia.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Camellia.RISCV64.ModesLit
import VerifiedGarbage.Proof.Camellia.RISCV64.FbFinalLit

/-! # Camellia-OFB on RISC-V -/

@[expose] public section

namespace VG.Artifacts.CamelliaOfb.RISCV64

def artifacts : List Artifact := [
  Spec.Camellia.ofbApi.artifact RISCV64.target Proof.Camellia.RISCV64.Scrub.ofbReg,
  Spec.Camellia.ofbFinalApi.artifact RISCV64.target Proof.Camellia.RISCV64.Scrub.ofbFinalReg]

end VG.Artifacts.CamelliaOfb.RISCV64
