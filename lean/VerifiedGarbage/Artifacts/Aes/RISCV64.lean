module

public import VerifiedGarbage.Proof.Aes.RISCV64.Scrub
public import VerifiedGarbage.Impl.Aes.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit

/-! # AES (FIPS 197) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Aes.RISCV64

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.expandKey
    verified := Proof.Aes.RISCV64.Scrub.expandKey_scrubbed }]

end VG.Artifacts.Aes.RISCV64
