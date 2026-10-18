module

public import VerifiedGarbage.Proof.Bignum.Arm.ReverseEncoding

/-! # The same byte reversal implements RSA's I2OSP -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm

/-- The complete loop exports the exact original little-endian integer. -/
theorem ReverseInv.i2osp {s0 s : State} {src dst : BitVec 32} {n : Nat}
    (inv : ReverseInv s0 (src + BitVec.ofNat 32 (n - 1)) dst n n s)
    (srcFit : src.toNat + n ≤ 2 ^ 32) (dstFit : dst.toNat + n ≤ 2 ^ 32) :
    Spec.Rsa.bytesAt s.mem (State.addr dst) n = Spec.Rsa.i2osp (s0.mem.read (State.addr src) n).toNat n := by
  apply reversed_i2osp
  intro j hj
  have h := inv.copied j hj
  rw [addr_add (by omega), reverse_source_addr src srcFit hj] at h
  exact h

end VG.Proof.Bignum.Arm
