module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.X448.RISCV64.R64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # X448 (RFC 7748) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.X448.RISCV64

def artifacts : List Artifact := [
  Spec.X448.x448Api.artifact RISCV64.target {
    code := Impl.X448.RISCV64.R64.x448
    verified := Proof.X448.RISCV64.R64.x448_verified }]

end VG.Artifacts.X448.RISCV64
