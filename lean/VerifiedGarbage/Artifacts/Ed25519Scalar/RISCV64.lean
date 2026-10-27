module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's reduction of a 64-byte scalar modulo `L`, on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed25519Scalar.RISCV64

def artifacts : List Artifact := [
  Spec.Ed25519.scalarReduceApi.artifact RISCV64.target {
    notes := ["Uses only caller-saved registers and no stack. The function reduces all 512 input \
      bits from the top, one at a time, in eight 32-bit limbs in `scratch` (rounded up to a \
      multiple of 8, since the contract states no alignment): the remainder doubled with the bit \
      as the carry in, then `L` subtracted (as an addition of `2^256 - L`, whose carry out says \
      whether the remainder was at least `L`) and selected with a mask. The result is written a \
      byte at a time."]
    code := Impl.Ed25519.RISCV64.scalarReduce
    verified := Proof.Ed25519.RISCV64.scalarReduce_verified }]

end VG.Artifacts.Ed25519Scalar.RISCV64
