module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's reduction of a 64-byte scalar modulo `L`, on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed25519Scalar.RISCV64

def artifacts : List Artifact := [
  Spec.Ed25519.scalarReduceApi.artifact RISCV64.target {
    code := Impl.Ed25519.RISCV64.scalarReduce
    verified := Proof.Ed25519.RISCV64.scalarReduce_verified }]

end VG.Artifacts.Ed25519Scalar.RISCV64
