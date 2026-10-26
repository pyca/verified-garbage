module

public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.X25519.RISCV64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # X25519 (RFC 7748) on RISC-V -/

@[expose] public section

namespace VG.Artifacts.X25519.RISCV64

def artifacts : List Artifact := [
  Spec.X25519.x25519Api.artifact RISCV64.target {
    notes := ["The function uses only caller-saved registers and no stack. Field elements are \
      eight 32-bit limbs, one to a word of `scratch` (rounded up to a multiple of 8, since the \
      contract states no alignment), multiplied row by row with `mul` (each step \
      `a_i b_j + acc + carry` fits in 64 bits) and reduced with `2^256 = 38` (mod p); the \
      inversion is square-and-multiply over the public bits of `p - 2`. The u-coordinate and the \
      result are read and written a byte at a time."]
    code := Impl.X25519.RISCV64.x25519
    verified := Proof.X25519.RISCV64.x25519_verified }]

end VG.Artifacts.X25519.RISCV64
