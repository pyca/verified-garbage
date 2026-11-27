module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ccm.Contract
import VerifiedGarbage.Proof.AesCcm.RISCV64.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-CCM (NIST SP 800-38C) on RISC-V -/

namespace VG.Artifacts.AesCcm.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Ccm.sealApi.artifact RISCV64.target {
    code := Impl.AesCcm.RISCV64.Fn.«seal»
    verified := Proof.AesCcm.RISCV64.Scrub.seal_scrubbed },
  Spec.Ccm.openApi.artifact RISCV64.target {
    code := Impl.AesCcm.RISCV64.Fn.«open»
    verified := Proof.AesCcm.RISCV64.Scrub.open_scrubbed }]

spec_apis artifacts

end VG.Artifacts.AesCcm.RISCV64
