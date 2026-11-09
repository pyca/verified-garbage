module

public import VerifiedGarbage.Proof.Aes.RISCV64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit

/-! # AES (FIPS 197) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Aes.RISCV64

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchWiped 512 .a3 64 Impl.Aes.RISCV64.expandKey
    stack := 512
    verified := Proof.Aes.RISCV64.expandKey_framed }]

end VG.Artifacts.Aes.RISCV64
