module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Law
public import VerifiedGarbage.Proof.Sm4Gcm.RISCV64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

import VerifiedGarbage.Proof.Sm4.RISCV64.Lit
import VerifiedGarbage.Proof.Sm4.RISCV64.ModesLit
import VerifiedGarbage.Proof.Gcm.RISCV64.Lit

/-! # SM4-GCM (NIST SP 800-38D, RFC 8998) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm4Gcm.RISCV64

open VG.Proof.Sm4Gcm.RISCV64.Scrub

def artifacts : List Artifact := [
  Spec.Sm4.Gcm.initApi.artifact RISCV64.target initReg,
  Spec.Sm4.Gcm.sealApi.artifact RISCV64.target sealReg,
  Spec.Sm4.Gcm.openApi.artifact RISCV64.target openReg,
  Spec.Sm4.Gcm.streamInitApi.artifact RISCV64.target streamInitReg,
  Spec.Sm4.Gcm.streamAadApi.artifact RISCV64.target streamAadReg,
  Spec.Sm4.Gcm.streamEncryptApi.artifact RISCV64.target streamEncryptReg,
  Spec.Sm4.Gcm.streamDecryptApi.artifact RISCV64.target streamDecryptReg,
  Spec.Sm4.Gcm.streamFinishApi.artifact RISCV64.target streamFinishReg,
  Spec.Sm4.Gcm.streamVerifyApi.artifact RISCV64.target streamVerifyReg]

end VG.Artifacts.Sm4Gcm.RISCV64
