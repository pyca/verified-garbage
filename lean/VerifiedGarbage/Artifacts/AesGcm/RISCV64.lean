module

public import VerifiedGarbage.Proof.AesGcm.RISCV64.Gather.Verified
public import VerifiedGarbage.Proof.Gcm.RISCV64.Law
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Gcm.RISCV64.Lit

/-! # AES-GCM (NIST SP 800-38D) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesGcm.RISCV64

def artifacts : List Artifact := [
  Spec.Gcm.initApi.artifact RISCV64.target Proof.AesGcm.RISCV64.Scrub.initReg,
  Spec.Gcm.streamInitApi.artifact RISCV64.target Proof.AesGcm.RISCV64.Scrub.streamInitReg,
  Spec.Gcm.streamAadApi.artifact RISCV64.target Proof.AesGcm.RISCV64.Scrub.streamAadReg,
  Spec.Gcm.streamEncryptApi.artifact RISCV64.target Proof.AesGcm.RISCV64.Scrub.streamEncryptReg,
  Spec.Gcm.streamDecryptApi.artifact RISCV64.target Proof.AesGcm.RISCV64.Scrub.streamDecryptReg,
  Spec.Gcm.streamFinishApi.artifact RISCV64.target Proof.AesGcm.RISCV64.Scrub.streamFinishReg,
  Spec.Gcm.streamVerifyApi.artifact RISCV64.target Proof.AesGcm.RISCV64.Scrub.streamVerifyReg,
  Spec.Gcm.sealApi.artifact RISCV64.target Proof.AesGcm.RISCV64.Scrub.sealReg,
  Spec.Gcm.openApi.artifact RISCV64.target Proof.AesGcm.RISCV64.Scrub.openReg,
  Spec.Gcm.sealGatherApi.artifact RISCV64.target Proof.AesGcm.RISCV64.Scrub.sealGatherReg,
  Spec.Gcm.openToApi.artifact RISCV64.target Proof.AesGcm.RISCV64.Scrub.openToReg]

end VG.Artifacts.AesGcm.RISCV64
