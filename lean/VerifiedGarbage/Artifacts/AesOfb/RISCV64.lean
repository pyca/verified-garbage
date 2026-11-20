module

public import VerifiedGarbage.Proof.Aes.RISCV64.Scrub
public import VerifiedGarbage.Impl.Aes.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # AES-OFB (NIST SP 800-38A §6.4) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesOfb.RISCV64

def artifacts : List Artifact := [
  Spec.Ofb.aesApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.ofb
    verified := .scrubbed Proof.Aes.RISCV64.Scrub.ofb_scrubbed },
  Spec.Ofb.aesFinalApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.ofbFinal
    verified := .scrubbed Proof.Aes.RISCV64.Scrub.ofbFinal_scrubbed }]

end VG.Artifacts.AesOfb.RISCV64
