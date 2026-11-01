module

public import VerifiedGarbage.Proof.AesCcm.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CCM (NIST SP 800-38C) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesCcm.RISCV64

open VG.Proof.AesCcm.RISCV64

def artifacts : List Artifact := [
  Spec.Ccm.sealApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 Impl.AesCcm.RISCV64.«seal»
    stack := 2592
    verified := seal_framed },
  Spec.Ccm.openApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 Impl.AesCcm.RISCV64.«open»
    stack := 2592
    verified := open_framed }]

end VG.Artifacts.AesCcm.RISCV64
