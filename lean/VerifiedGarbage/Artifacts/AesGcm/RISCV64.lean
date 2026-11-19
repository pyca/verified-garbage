module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Law
public import VerifiedGarbage.Proof.AesGcm.RISCV64.Bitslice
public import VerifiedGarbage.Proof.AesGcm.RISCV64.StreamBs
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OneBs
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OpenBs
public import VerifiedGarbage.Proof.AesGcm.RISCV64.OpenToBs
public import VerifiedGarbage.Proof.AesGcm.RISCV64.GatherBs
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Gcm.RISCV64.Lit

/-! # AES-GCM (NIST SP 800-38D) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesGcm.RISCV64

open VG.Proof.AesGcm.RISCV64

def artifacts : List Artifact := [
  Spec.Gcm.initApi.artifact RISCV64.target initReg,
  Spec.Gcm.streamInitApi.artifact RISCV64.target streamInitReg,
  Spec.Gcm.streamAadApi.artifact RISCV64.target streamAadReg,
  Spec.Gcm.bitsliceApi.artifact RISCV64.target Bitslice.bitsliceReg,
  Spec.Gcm.streamEncryptBitslicedApi.artifact RISCV64.target streamEncryptBsReg,
  Spec.Gcm.streamDecryptBitslicedApi.artifact RISCV64.target streamDecryptBsReg,
  Spec.Gcm.streamFinishBitslicedApi.artifact RISCV64.target streamFinishBsReg,
  Spec.Gcm.streamVerifyBitslicedApi.artifact RISCV64.target streamVerifyBsReg,
  Spec.Gcm.sealBitslicedApi.artifact RISCV64.target sealBsReg,
  Spec.Gcm.openBitslicedApi.artifact RISCV64.target openBsReg,
  Spec.Gcm.openToBitslicedApi.artifact RISCV64.target openToBsReg,
  Spec.Gcm.sealGatherBitslicedApi.artifact RISCV64.target GatherBs.sealGatherBsReg]

end VG.Artifacts.AesGcm.RISCV64
