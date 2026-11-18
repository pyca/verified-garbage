module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Blowfish.RISCV64.ModesLit

/-! # Blowfish-CBC on RISC-V -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.RISCV64

def artifacts : List Artifact := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact RISCV64.target Proof.Blowfish.RISCV64.Scrub.cbcEncryptChainedReg,
  Spec.Blowfish.cbcDecryptChainedApi.artifact RISCV64.target Proof.Blowfish.RISCV64.Scrub.cbcDecryptChainedReg]

end VG.Artifacts.BlowfishCbc.RISCV64
