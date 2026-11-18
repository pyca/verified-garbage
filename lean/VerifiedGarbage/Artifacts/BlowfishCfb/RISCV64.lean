module

public import VerifiedGarbage.Proof.Blowfish.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Blowfish.RISCV64.ModesLit
import VerifiedGarbage.Proof.Blowfish.RISCV64.FbFinalLit

/-! # Blowfish-CFB64 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.RISCV64

def artifacts : List Artifact := [
  Spec.Blowfish.cfbEncryptApi.artifact RISCV64.target Proof.Blowfish.RISCV64.Scrub.cfbEncryptReg,
  Spec.Blowfish.cfbDecryptApi.artifact RISCV64.target Proof.Blowfish.RISCV64.Scrub.cfbDecryptReg,
  Spec.Blowfish.cfbEncryptFinalApi.artifact RISCV64.target Proof.Blowfish.RISCV64.Scrub.cfbEncryptFinalReg,
  Spec.Blowfish.cfbDecryptFinalApi.artifact RISCV64.target Proof.Blowfish.RISCV64.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.BlowfishCfb.RISCV64
