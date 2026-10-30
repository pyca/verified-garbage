module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's `(r + k s) mod L`, on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed25519MulAdd.RISCV64

def artifacts : List Artifact := [
  Spec.Ed25519.scalarMulAddApi.artifact RISCV64.target {
    code := Impl.Ed25519.RISCV64.scalarMulAdd
    verified := Proof.Ed25519.RISCV64.scalarMulAdd_verified }]

end VG.Artifacts.Ed25519MulAdd.RISCV64
