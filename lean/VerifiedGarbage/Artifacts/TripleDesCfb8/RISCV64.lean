module

public import VerifiedGarbage.Proof.TripleDes.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.TripleDes.RISCV64.ModesLit

/-! # Triple DES-CFB8 on RISC-V -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb8.RISCV64

def artifacts : List Artifact := [
  Spec.TripleDes.cfb8EncryptApi.artifact RISCV64.target Proof.TripleDes.RISCV64.Scrub.cfb8EncryptReg,
  Spec.TripleDes.cfb8DecryptApi.artifact RISCV64.target Proof.TripleDes.RISCV64.Scrub.cfb8DecryptReg]

end VG.Artifacts.TripleDesCfb8.RISCV64
