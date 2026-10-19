module

import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.AddrArith

/-! # Byte-level consequences of packed-limb zeroing -/

@[expose] public section

namespace VG.Proof.Bignum
open VG VG.Proof.Mont

theorem read_eq_val32 (m : Mem) (base : Addr) : ∀ (n d : Nat),
    (m.read (off base d) (4 * n)).toNat = val32 m base d n
  | 0, d => rfl
  | n + 1, d => by
    rw [show 4 * (n + 1) = 4 * n + 4 from rfl, read_toNat_add, val32,
      ← read_eq_val32 m base n (d + 4), Offset.add_add]
    congr 1

theorem byte_zero_of_val32 {m : Mem} {base : Addr} {n d j : Nat}
    (zero : val32 m base d n = 0) (hj : j < 4 * n) :
    m (off base d + BitVec.ofNat 64 j) = 0 := by
  have hz : m.read (off base d) (4 * n) = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [read_eq_val32, zero]
    rfl
  rw [← Mem.extractLsb'_read m _ hj, hz]
  apply BitVec.eq_of_toNat_eq
  simp

theorem read_zero_bytes (m : Mem) (a : Addr) (n : Nat)
    (zero : ∀ j < n, m (a + BitVec.ofNat 64 j) = 0) :
    (m.read a n).toNat = 0 := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have z : m a = 0 := by simpa using zero 0 (by omega)
    rw [read_toNat_succ, z, ih (a + 1)]
    · rfl
    · intro j hj
      have e : a + 1 + BitVec.ofNat 64 j = a + BitVec.ofNat 64 (j + 1) := by
        change a + BitVec.ofNat 64 1 + BitVec.ofNat 64 j = _
        rw [Offset.add_add, Nat.add_comm 1]
      rw [e]
      exact zero _ (by omega)

/-- High zero padding does not change the integer read from a shorter byte string. -/
theorem val32_zero_extension (m : Mem) (a : Addr) {n k : Nat} (fit : k ≤ 4 * n)
    (padding : ∀ j, k ≤ j → j < 4 * n → m (a + BitVec.ofNat 64 j) = 0) :
    val32 m a 0 n = (m.read a k).toNat := by
  rw [← read_eq_val32, show off a 0 = a by simp [off],
    show 4 * n = (4 * n - k) + k by omega, read_toNat_add]
  have z : (m.read (a + BitVec.ofNat 64 k) (4 * n - k)).toNat = 0 := by
    apply read_zero_bytes
    intro j hj
    rw [Offset.add_add]
    exact padding _ (by omega) (by omega)
  rw [z, Nat.mul_zero, Nat.add_zero]

end VG.Proof.Bignum
