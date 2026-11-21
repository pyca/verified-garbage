module

public import VerifiedGarbage.Proof.Aes.RISCV64.Scrub
public import VerifiedGarbage.Impl.Aes.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print
import VerifiedGarbage.Proof.AesCtr.RISCV64.Lit

/-! # AES-CTR (NIST SP 800-38A §6.5) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesCtr.RISCV64

def artifacts : List Artifact := [
  Spec.Ctr.aesApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.ctr
    verified := Proof.Aes.RISCV64.Scrub.ctr_scrubbed },
  Spec.Ctr.aesFinalApi.artifact RISCV64.target {
    code := Impl.Aes.RISCV64.Fn.ctrFinal
    verified := Proof.Aes.RISCV64.Scrub.ctrFinal_scrubbed }]

end VG.Artifacts.AesCtr.RISCV64
