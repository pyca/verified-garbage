module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit
import VerifiedGarbage.Proof.TripleDes.RISCV64.FbFinalLit

/-! # Triple DES-CFB64 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.RISCV64

def artifacts : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact RISCV64.target Proof.TripleDes.RISCV64.Scrub.cfbEncryptReg,
  Spec.TripleDes.cfbDecryptApi.artifact RISCV64.target Proof.TripleDes.RISCV64.Scrub.cfbDecryptReg,
  Spec.TripleDes.cfbEncryptFinalApi.artifact RISCV64.target Proof.TripleDes.RISCV64.Scrub.cfbEncryptFinalReg,
  Spec.TripleDes.cfbDecryptFinalApi.artifact RISCV64.target Proof.TripleDes.RISCV64.Scrub.cfbDecryptFinalReg]

end VG.Artifacts.TripleDesCfb.RISCV64
