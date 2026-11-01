module

public import VerifiedGarbage.Proof.CmacAes.RISCV64.Verified
public import VerifiedGarbage.Proof.CmacAes.Stream.RISCV64.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CMAC (NIST SP 800-38B) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.CmacAes.RISCV64

open VG.Proof.CmacAes.RISCV64

def artifacts : List Artifact := [
  Spec.Cmac.aesInitApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratch 2304 .a3 Impl.CmacAes.Stream.RISCV64.init
    stack := 2304
    verified := Proof.CmacAes.Stream.RISCV64.init_framed },
  Spec.Cmac.aesAbsorbApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratch 2304 .a5 Impl.CmacAes.Stream.RISCV64.absorb
    stack := 2304
    verified := Proof.CmacAes.Stream.RISCV64.absorb_framed },
  Spec.Cmac.aesFinishApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratch 2304 .a4 Impl.CmacAes.Stream.RISCV64.finish
    stack := 2304
    verified := Proof.CmacAes.Stream.RISCV64.finish_framed }]

end VG.Artifacts.CmacAes.RISCV64
