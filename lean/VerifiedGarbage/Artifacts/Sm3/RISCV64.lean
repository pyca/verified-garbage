module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Sm3.RISCV64.Scrub
public import VerifiedGarbage.Impl.Sm3.RISCV64.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.RISCV64.Print

/-! # SM3 (GB/T 32905-2016) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Sm3.RISCV64

def artifacts : List Artifact := [
  Spec.Sm3.initApi.artifact RISCV64.target {
    code := Impl.Sm3.RISCV64.Fn.init
    verified := Proof.Sm3.RISCV64.init_scrubbed },
  Spec.Sm3.updateApi.artifact RISCV64.target {
    code := Impl.Sm3.RISCV64.Fn.update
    verified := Proof.Sm3.RISCV64.update_scrubbed },
  Spec.Sm3.finalizeApi.artifact RISCV64.target {
    code := Impl.Sm3.RISCV64.Fn.finalize
    verified := Proof.Sm3.RISCV64.finalize_scrubbed }]

end VG.Artifacts.Sm3.RISCV64
