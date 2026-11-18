module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Blowfish.RISCV64.ModesLit
import VerifiedGarbage.Proof.Blowfish.RISCV64.FbFinalLit

/-! # Blowfish-OFB on RISC-V -/

@[expose] public section

namespace VG.Artifacts.BlowfishOfb.RISCV64

def artifacts : List Artifact := [
  Spec.Blowfish.ofbApi.artifact RISCV64.target Proof.Blowfish.RISCV64.Scrub.ofbReg,
  Spec.Blowfish.ofbFinalApi.artifact RISCV64.target Proof.Blowfish.RISCV64.Scrub.ofbFinalReg]

end VG.Artifacts.BlowfishOfb.RISCV64
