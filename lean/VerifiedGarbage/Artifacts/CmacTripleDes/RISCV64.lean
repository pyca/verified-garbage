module

public import VerifiedGarbage.Proof.CmacTripleDes.Stream.RISCV64.Frame
public import VerifiedGarbage.Impl.CmacTripleDes.Stream.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.CmacTripleDes.RISCV64

def artifacts : List Artifact := [
  Spec.Cmac.tdesStreamInitApi.artifact RISCV64.target {
    code := Impl.CmacTripleDes.Stream.RISCV64.Fn.init
    verified := .scrubbed Proof.CmacTripleDes.Stream.RISCV64.Scrub.init_scrubbed },
  Spec.Cmac.tdesAbsorbApi.artifact RISCV64.target {
    code := Impl.CmacTripleDes.Stream.RISCV64.Fn.absorb
    verified := .scrubbed Proof.CmacTripleDes.Stream.RISCV64.Scrub.absorb_scrubbed },
  Spec.Cmac.tdesFinishApi.artifact RISCV64.target {
    code := Impl.CmacTripleDes.Stream.RISCV64.Fn.finish
    verified := .scrubbed Proof.CmacTripleDes.Stream.RISCV64.Scrub.finish_scrubbed }]

end VG.Artifacts.CmacTripleDes.RISCV64
