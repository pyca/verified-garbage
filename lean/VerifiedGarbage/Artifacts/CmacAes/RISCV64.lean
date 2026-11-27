module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cmac.Contract
import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Scrub
import VerifiedGarbage.Impl.CmacAes.Stream.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CMAC (NIST SP 800-38B) on RISC-V -/

namespace VG.Artifacts.CmacAes.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Cmac.aesInitApi.artifact RISCV64.target {
    code := Impl.CmacAes.Stream.RISCV64.Fn.init
    verified := Proof.CmacAes.Stream.RISCV64.Scrub.init_scrubbed },
  Spec.Cmac.aesAbsorbApi.artifact RISCV64.target {
    code := Impl.CmacAes.Stream.RISCV64.Fn.absorb
    verified := Proof.CmacAes.Stream.RISCV64.Scrub.absorb_scrubbed },
  Spec.Cmac.aesFinishApi.artifact RISCV64.target {
    code := Impl.CmacAes.Stream.RISCV64.Fn.finish
    verified := Proof.CmacAes.Stream.RISCV64.Scrub.finish_scrubbed }]

spec_apis artifacts

end VG.Artifacts.CmacAes.RISCV64
