module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Aes.Contract
import VerifiedGarbage.Proof.Aes.RISCV64.Scrub
import VerifiedGarbage.Impl.Aes.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Aes.RISCV64.CodeLit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES (FIPS 197) on RISC-V -/

namespace VG.Artifacts.Aes.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Aes.expandKeyApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.expandKey
    verified := Proof.Aes.RISCV64.Scrub.expandKey_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Aes.RISCV64
