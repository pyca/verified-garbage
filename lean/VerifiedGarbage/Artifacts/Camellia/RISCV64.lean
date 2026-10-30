module

public import VerifiedGarbage.Proof.Camellia.RISCV64.Verified
public import VerifiedGarbage.Proof.Camellia.RISCV64.KeyVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.RISCV64.Lit

/-! # Camellia artifacts on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Camellia.RISCV64

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 3200 .a3 400 Impl.Camellia.RISCV64.expandKey
    stack := 3200
    verified := Proof.Camellia.RISCV64.expandKey_framed },
  Spec.Camellia.ecbEncryptApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 3200 .a4 400
      (Impl.Camellia.RISCV64.ecb .encrypt)
    stack := 3200
    verified := Proof.Camellia.RISCV64.ecb_framed .encrypt },
  Spec.Camellia.ecbDecryptApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 3200 .a4 400
      (Impl.Camellia.RISCV64.ecb .decrypt)
    stack := 3200
    verified := Proof.Camellia.RISCV64.ecb_framed .decrypt }]

end VG.Artifacts.Camellia.RISCV64
