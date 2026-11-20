module

public import VerifiedGarbage.Proof.AesCcm.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # AES-CCM (NIST SP 800-38C) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesCcm.RISCV64

def artifacts : List Artifact := [
  Spec.Ccm.sealApi.artifact RISCV64.target {
    code := Impl.AesCcm.RISCV64.Fn.«seal»
    verified := .scrubbed Proof.AesCcm.RISCV64.Scrub.seal_scrubbed },
  Spec.Ccm.openApi.artifact RISCV64.target {
    code := Impl.AesCcm.RISCV64.Fn.«open»
    verified := .scrubbed Proof.AesCcm.RISCV64.Scrub.open_scrubbed }]

end VG.Artifacts.AesCcm.RISCV64
