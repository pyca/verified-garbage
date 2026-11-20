module

public import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Scrub
public import VerifiedGarbage.Impl.CmacAes.Stream.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # AES-CMAC (NIST SP 800-38B) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.CmacAes.RISCV64

def artifacts : List Artifact := [
  Spec.Cmac.aesInitApi.artifact RISCV64.target {
    code := Impl.CmacAes.Stream.RISCV64.Fn.init
    verified := .scrubbed Proof.CmacAes.Stream.RISCV64.Scrub.init_scrubbed },
  Spec.Cmac.aesAbsorbApi.artifact RISCV64.target {
    code := Impl.CmacAes.Stream.RISCV64.Fn.absorb
    verified := .scrubbed Proof.CmacAes.Stream.RISCV64.Scrub.absorb_scrubbed },
  Spec.Cmac.aesFinishApi.artifact RISCV64.target {
    code := Impl.CmacAes.Stream.RISCV64.Fn.finish
    verified := .scrubbed Proof.CmacAes.Stream.RISCV64.Scrub.finish_scrubbed }]

end VG.Artifacts.CmacAes.RISCV64
