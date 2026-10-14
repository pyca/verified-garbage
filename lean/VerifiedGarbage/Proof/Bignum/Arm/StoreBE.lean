module

public import VerifiedGarbage.Proof.Bignum.Arm.ReverseEncoding
import VerifiedGarbage.Proof.Rsa.Octets
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # The same byte reversal implements RSA's I2OSP -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm

/-- Reversing a little-endian memory read produces its I2OSP encoding. -/
theorem reversed_i2osp (m m' : Mem) (p q : Addr) (n : Nat)
    (bytes : ∀ j < n, m' (q + BitVec.ofNat 64 j) = m (p + BitVec.ofNat 64 (n - 1 - j))) :
    Spec.Rsa.bytesAt m' q n = Spec.Rsa.i2osp (m.read p n).toNat n := by
  have value : (m.read p n).toNat = Spec.Rsa.os2ip (Spec.Rsa.bytesAt m' q n) := by
    apply reversed_read
    intro j hj
    have h := bytes (n - 1 - j) (by omega)
    rw [show n - 1 - (n - 1 - j) = j by omega] at h
    exact h.symm
  rw [value]
  have len : (Spec.Rsa.bytesAt m' q n).length = n := by
    simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  simpa only [len] using (VG.Proof.Rsa.i2osp_os2ip (Spec.Rsa.bytesAt m' q n)).symm

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
