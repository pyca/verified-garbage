module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Ed25519.RISCV64.ScalarVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Ed25519's `(r + k s) mod L`, on RISC-V -/

@[expose] public section

namespace VG.Artifacts.Ed25519MulAdd.RISCV64

def artifacts : List Artifact := [
  Spec.Ed25519.scalarMulAddApi.artifact RISCV64.target {
    notes := ["Uses only caller-saved registers and no stack. The function reads `r`, `k` and \
      `s` a byte at a time into `scratch` (rounded up to a multiple of 8, since the contract \
      states no alignment), computes the 512-bit `k s` row by row with `mul` (X25519's RISC-V \
      product, without its reduction), adds `r`, and reduces the sum bit by bit as \
      `vg_ed25519_scalar_reduce` does."]
    code := Impl.Ed25519.RISCV64.scalarMulAdd
    verified := Proof.Ed25519.RISCV64.scalarMulAdd_verified }]

end VG.Artifacts.Ed25519MulAdd.RISCV64
