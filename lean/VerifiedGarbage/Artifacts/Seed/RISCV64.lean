module

public import VerifiedGarbage.Proof.Seed.RISCV64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.RISCV64.Lit

/-! # SEED artifacts on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Seed.RISCV64

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 1040 .a2 129 Impl.Seed.RISCV64.expandKey
    stack := 1040
    verified := Proof.Seed.RISCV64.expandKey_framed },
  Spec.Seed.ecbEncryptApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 1040 .a3 129 (Impl.Seed.RISCV64.ecb .encrypt)
    stack := 1040
    verified := Proof.Seed.RISCV64.ecb_framed .encrypt },
  Spec.Seed.ecbDecryptApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 1040 .a3 129 (Impl.Seed.RISCV64.ecb .decrypt)
    stack := 1040
    verified := Proof.Seed.RISCV64.ecb_framed .decrypt }]

end VG.Artifacts.Seed.RISCV64
