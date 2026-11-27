module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ofb.Contract
public import VerifiedGarbage.Spec.Ofb.Final
import VerifiedGarbage.Proof.Aes.RISCV64.Scrub
import VerifiedGarbage.Impl.Aes.RISCV64.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-OFB (NIST SP 800-38A §6.4) on RISC-V -/

namespace VG.Artifacts.AesOfb.RISCV64

public def artifacts : List (Artifact RISCV64.target) := [
  Spec.Ofb.aesApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.ofb
    verified := Proof.Aes.RISCV64.Scrub.ofb_scrubbed },
  Spec.Ofb.aesFinalApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.ofbFinal
    verified := Proof.Aes.RISCV64.Scrub.ofbFinal_scrubbed }]

spec_apis artifacts

end VG.Artifacts.AesOfb.RISCV64
