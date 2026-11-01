module

public import VerifiedGarbage.Proof.Sm4.RISCV64.KeyVerified
public import VerifiedGarbage.Proof.Sm4.RISCV64.Verified
public import VerifiedGarbage.Proof.Sm4.RISCV64.PreparedVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.RISCV64.Lit

/-! # SM4 artifacts on baseline RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm4.RISCV64

def artifacts : List Artifact := [
  Spec.Sm4.expandKeyApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 3168 .a2 396 Impl.Sm4.RISCV64.expandKey
    stack := 3168
    verified := Proof.Sm4.RISCV64.expandKey_framed },
  Spec.Sm4.ecbEncryptApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 3168 .a3 396 (Impl.Sm4.RISCV64.ecb .encrypt)
    stack := 3168
    verified := Proof.Sm4.RISCV64.ecb_framed .encrypt },
  Spec.Sm4.ecbDecryptApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 3168 .a3 396 (Impl.Sm4.RISCV64.ecb .decrypt)
    stack := 3168
    verified := Proof.Sm4.RISCV64.ecb_framed .decrypt }]

end VG.Artifacts.Sm4.RISCV64
