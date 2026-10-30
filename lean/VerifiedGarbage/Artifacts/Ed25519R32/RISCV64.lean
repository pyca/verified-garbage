module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed25519.RISCV64.FieldVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's point addition, in radix `2^32`, on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed25519R32.RISCV64

open VG.Spec.Ed25519.Point32 VG.Impl.Ed25519.RISCV64 VG.Proof.Ed25519.RISCV64

def artifacts : List Artifact := [
  addApi.artifact RISCV64.target {
    code := addFn
    verified := addFn_verified }]

end VG.Artifacts.Ed25519R32.RISCV64
