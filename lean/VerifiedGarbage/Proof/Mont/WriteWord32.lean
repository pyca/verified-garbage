module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Omega

/-! # Setting a high word of a small number, shared by 32-bit targets -/

@[expose] public section
namespace VG.Proof.Mont
open VG

/-- Word `i` written, of a number below `2^(32 i)`. -/
theorem val32_write_word (m : Mem) (base : Addr) {d i k : Nat} (v : BitVec 32) (hi : i < k)
    (fit : d + 4 * k ≤ 2 ^ 64) (hl : val32 m base d k < 2 ^ (32 * i)) :
    val32 (m.writeW (off base (d + 4 * i)) v) base d k = val32 m base d k + 2 ^ (32 * i) * v.toNat := by
  have o := writeW32_outside m base (d := d + 4 * i) v (by omega)
  obtain ⟨r, rfl⟩ : ∃ r, k = i + (r + 1) := ⟨k - i - 1, by omega⟩
  rw [val32_append _ base d i (r + 1), val32_append m base d i (r + 1)]
  rw [val32_append m base d i (r + 1)] at hl
  simp only [val32] at hl ⊢
  have e1 : val32 (m.writeW (off base (d + 4 * i)) v) base d i = val32 m base d i := o.val32 (by omega) (by omega)
  have e2 : w32 (m.writeW (off base (d + 4 * i)) v) base (d + 4 * i) = v.toNat := by
    exact w32_write_self ..
  have e3 : val32 (m.writeW (off base (d + 4 * i)) v) base (d + 4 * i + 4) r = val32 m base (d + 4 * i + 4) r :=
    o.val32 (by omega) (by omega)
  have lo := val32_lt m base d i
  have z : w32 m base (d + 4 * i) + 2 ^ 32 * val32 m base (d + 4 * i + 4) r = 0 := by
    rcases Nat.eq_zero_or_pos (w32 m base (d + 4 * i) + 2 ^ 32 * val32 m base (d + 4 * i + 4) r) with h | h
    · exact h
    · have := Nat.le_mul_of_pos_right (2 ^ (32 * i)) h; omega
  have z1 : w32 m base (d + 4 * i) = 0 := by omega
  have z2 : val32 m base (d + 4 * i + 4) r = 0 := by
    rcases Nat.eq_zero_or_pos (val32 m base (d + 4 * i + 4) r) with h | h
    · exact h
    · have := Nat.le_mul_of_pos_right (2 ^ 32) h; omega
  rw [e1, e2, e3, z1, z2]
  simp only [Nat.mul_zero, Nat.add_zero]


end VG.Proof.Mont
