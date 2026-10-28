module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.X448.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # X448 (RFC 7748) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.X448.RISCV64

def artifacts : List Artifact := [
  Spec.X448.x448Api.artifact RISCV64.target {
    notes := ["The function uses only caller-saved registers and no stack. Field elements are \
      fourteen 32-bit limbs, one to a word of `scratch` (rounded up to a multiple of 8), \
      multiplied row by row with `mul` (each step `a_i b_j + acc + carry` fits in 64 bits) and \
      reduced with `2^448 = 2^224 + 1` (mod p); the inversion is square-and-multiply over the \
      public bits of `p - 2`. The u-coordinate and the result are read and written a byte at a \
      time."]
    code := Impl.X448.RISCV64.x448
    verified := Proof.X448.RISCV64.x448_verified }]

end VG.Artifacts.X448.RISCV64
