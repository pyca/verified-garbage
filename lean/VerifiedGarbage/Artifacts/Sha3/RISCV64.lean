module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sha3.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # SHA-3 and SHAKE (FIPS 202) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sha3.RISCV64

def artifacts : List Artifact := [
  Spec.Sha3.absorbSha3_224Api.artifact RISCV64.target Proof.Sha3.RISCV64.absorbSha3_224Reg,
  Spec.Sha3.finalizeSha3_224Api.artifact RISCV64.target Proof.Sha3.RISCV64.finalizeSha3_224Reg,
  Spec.Sha3.absorbSha3_256Api.artifact RISCV64.target Proof.Sha3.RISCV64.absorbSha3_256Reg,
  Spec.Sha3.finalizeSha3_256Api.artifact RISCV64.target Proof.Sha3.RISCV64.finalizeSha3_256Reg,
  Spec.Sha3.absorbSha3_384Api.artifact RISCV64.target Proof.Sha3.RISCV64.absorbSha3_384Reg,
  Spec.Sha3.finalizeSha3_384Api.artifact RISCV64.target Proof.Sha3.RISCV64.finalizeSha3_384Reg,
  Spec.Sha3.absorbSha3_512Api.artifact RISCV64.target Proof.Sha3.RISCV64.absorbSha3_512Reg,
  Spec.Sha3.finalizeSha3_512Api.artifact RISCV64.target Proof.Sha3.RISCV64.finalizeSha3_512Reg,
  Spec.Sha3.absorbShake128Api.artifact RISCV64.target Proof.Sha3.RISCV64.absorbShake128Reg,
  Spec.Sha3.finalizeShake128Api.artifact RISCV64.target Proof.Sha3.RISCV64.finalizeShake128Reg,
  Spec.Sha3.squeezeShake128Api.artifact RISCV64.target Proof.Sha3.RISCV64.squeezeShake128Reg,
  Spec.Sha3.finalizeShake256Api.artifact RISCV64.target Proof.Sha3.RISCV64.finalizeShake256Reg,
  Spec.Sha3.squeezeShake256Api.artifact RISCV64.target Proof.Sha3.RISCV64.squeezeShake256Reg]

end VG.Artifacts.Sha3.RISCV64
