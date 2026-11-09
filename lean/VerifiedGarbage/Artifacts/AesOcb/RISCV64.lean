module

public import VerifiedGarbage.Proof.AesOcb.RISCV64.Init
public import VerifiedGarbage.Proof.AesOcb.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # AES-OCB (RFC 7253) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesOcb.RISCV64

open VG.Proof.AesOcb.RISCV64

def artifacts : List Artifact := [
  Spec.Ocb.initApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a3 Impl.AesGcm.RISCV64.init
    stack := 2560
    verified := init_framed },
  Spec.Ocb.sealApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 Impl.AesOcb.RISCV64.«seal»
    stack := 2592
    verified := Proof.AesOcb.seal_keyed seal_framed },
  Spec.Ocb.openApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratchArgs 2592 2 Impl.AesOcb.RISCV64.«open»
    stack := 2592
    verified := Proof.AesOcb.open_keyed open_framed }]

end VG.Artifacts.AesOcb.RISCV64
