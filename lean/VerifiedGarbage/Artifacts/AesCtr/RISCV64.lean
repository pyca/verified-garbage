module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ctr.Contract
public import VerifiedGarbage.Spec.Ctr.Final
import VerifiedGarbage.Proof.Aes.RISCV64.Scrub
import VerifiedGarbage.Impl.Aes.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.AesCtr.RISCV64.Lit
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CTR (NIST SP 800-38A §6.5) on RISC-V -/

namespace VG.Artifacts.AesCtr.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Ctr.aesApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.ctr
    verified := Proof.Aes.RISCV64.Scrub.ctr_scrubbed },
  Spec.Ctr.aesFinalApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.ctrFinal
    verified := Proof.Aes.RISCV64.Scrub.ctrFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.AesCtr.RISCV64
