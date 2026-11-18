module

public import VerifiedGarbage.Proof.AesOcb.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # AES-OCB (RFC 7253) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesOcb.RISCV64

def artifacts : List Artifact := [
  Spec.Ocb.initApi.artifact RISCV64.target Proof.AesOcb.RISCV64.Scrub.initReg,
  Spec.Ocb.sealApi.artifact RISCV64.target Proof.AesOcb.RISCV64.Scrub.sealReg,
  Spec.Ocb.openApi.artifact RISCV64.target Proof.AesOcb.RISCV64.Scrub.openReg]

end VG.Artifacts.AesOcb.RISCV64
