module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Equal packed numbers have equal low and high word ranges. -/

@[expose] public section
namespace VG.Proof.Mont
open VG

theorem word_toNat_val32 (m : Mem) (base : Addr) (d : Nat) :
    (word m base d).toNat = val32 m base d 2 := by
  rw [word_eq_w32]
  simp only [val32, Nat.mul_zero, Nat.add_zero]

theorem val32_parts {m m' : Mem} {base base' : Addr} {d d' j k : Nat}
    (value : val32 m base d (j + k) = val32 m' base' d' (j + k)) :
    val32 m base d j = val32 m' base' d' j ∧
      val32 m base (d + 4 * j) k = val32 m' base' (d' + 4 * j) k := by
  rw [val32_append, val32_append] at value
  have low := congrArg (fun x => x % 2 ^ (32 * j)) value
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (val32_lt m base d j),
    Nat.mod_eq_of_lt (val32_lt m' base' d' j)] at low
  refine ⟨low, ?_⟩
  rw [low] at value
  exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos _) (Nat.add_left_cancel value)

end VG.Proof.Mont
