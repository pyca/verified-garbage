module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha512.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sha512.RISCV64

def artifacts : List Artifact := [
  Spec.Sha512.init384Api.artifact RISCV64.target Proof.Sha512.RISCV64.init384Reg,
  Spec.Sha512.init512Api.artifact RISCV64.target Proof.Sha512.RISCV64.init512Reg,
  Spec.Sha512.init512_224Api.artifact RISCV64.target Proof.Sha512.RISCV64.init512_224Reg,
  Spec.Sha512.init512_256Api.artifact RISCV64.target Proof.Sha512.RISCV64.init512_256Reg,
  Spec.Sha512.updateApi.artifact RISCV64.target Proof.Sha512.RISCV64.updateReg,
  Spec.Sha512.finalizeApi.artifact RISCV64.target Proof.Sha512.RISCV64.finalizeReg,
  Spec.Sha512.finalize384Api.artifact RISCV64.target Proof.Sha512.RISCV64.finalize384Reg,
  Spec.Sha512.finalize512_256Api.artifact RISCV64.target Proof.Sha512.RISCV64.finalize512_256Reg,
  Spec.Sha512.finalize512_224Api.artifact RISCV64.target Proof.Sha512.RISCV64.finalize512_224Reg,
  Spec.Sha512.digest384Api.artifact RISCV64.target Proof.Sha512.RISCV64.digest384Reg,
  Spec.Sha512.digest512Api.artifact RISCV64.target Proof.Sha512.RISCV64.digest512Reg,
  Spec.Sha512.digest512_224Api.artifact RISCV64.target Proof.Sha512.RISCV64.digest512_224Reg,
  Spec.Sha512.digest512_256Api.artifact RISCV64.target Proof.Sha512.RISCV64.digest512_256Reg]

end VG.Artifacts.Sha512.RISCV64
