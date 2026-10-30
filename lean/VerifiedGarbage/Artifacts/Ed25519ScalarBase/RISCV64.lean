module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarBaseVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's `[s] B`, encoded, on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed25519ScalarBase.RISCV64

def artifacts : List Artifact := [
  Spec.Ed25519.scalarBaseApi.artifact RISCV64.target {
    code := Impl.Ed25519.RISCV64.scalarBase
    verified := Proof.Ed25519.RISCV64.scalarBase_verified }]

end VG.Artifacts.Ed25519ScalarBase.RISCV64
