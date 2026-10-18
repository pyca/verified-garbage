module

public import VerifiedGarbage.Proof.Bignum.Arm.ReverseRegion
public import VerifiedGarbage.Proof.Bignum.ReverseEncoding

/-! # Byte reversal implements RSA's OS2IP -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
export VG.Proof.Bignum (reversed_read reversed_i2osp)
open VG VG.Arm VG.Proof.Mont

/-- The complete loop computes the integer of the original big-endian input. -/
theorem ReverseInv.os2ip {s0 s : State} {src dst : BitVec 32} {n : Nat}
    (inv : ReverseInv s0 (src + BitVec.ofNat 32 (n - 1)) dst n n s)
    (srcFit : src.toNat + n ≤ 2 ^ 32) (dstFit : dst.toNat + n ≤ 2 ^ 32) :
    (s.mem.read (State.addr dst) n).toNat = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem (State.addr src) n) := by
  apply reversed_read
  intro j hj
  have h := inv.copied j hj
  rw [addr_add (by omega), reverse_source_addr src srcFit hj] at h
  exact h

end VG.Proof.Bignum.Arm
