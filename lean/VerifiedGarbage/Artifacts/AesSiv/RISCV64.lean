module

public import VerifiedGarbage.Proof.AesSiv.RISCV64.Init
public import VerifiedGarbage.Proof.AesSiv.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-SIV (RFC 5297) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.AesSiv.RISCV64

open VG.Proof.AesSiv.RISCV64

def artifacts : List Artifact := [
  Spec.Siv.initApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratch 2560 .a3 Impl.AesSiv.RISCV64.init
    stack := 2560
    verified := init_framed },
  Spec.Siv.encryptApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratch 2576 .a7 Impl.AesSiv.RISCV64.encrypt
    stack := 2576
    verified := encrypt_framed },
  Spec.Siv.decryptApi.artifact RISCV64.target {
    code := Impl.StackScratch.RISCV64.withStackScratch 2576 .a7 Impl.AesSiv.RISCV64.decrypt
    stack := 2576
    verified := decrypt_framed }]

end VG.Artifacts.AesSiv.RISCV64
