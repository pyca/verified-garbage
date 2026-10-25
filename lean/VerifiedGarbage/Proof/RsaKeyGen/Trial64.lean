module

public import VerifiedGarbage.Proof.RsaKeyGen.Table
public import VerifiedGarbage.Proof.Framework.PowLit

/-! # Trial-division reduction of 64-bit words with a 64-bit inverse -/

@[expose] public section
namespace VG.Proof.RsaKeyGen

/-- Montgomery reduction of X by 2^64: exact, bounded, and congruent to
X times the inverse radix modulo the odd trial divisor. -/
theorem redc64_math {X s sv : Nat} (hinv : (s * sv + 1) % 2 ^ 64 = 0) (hX : X < s * 2 ^ 64) :
    (X + X * sv % 2 ^ 64 * s) % 2 ^ 64 = 0 ∧
    (X + X * sv % 2 ^ 64 * s) / 2 ^ 64 < 2 * s ∧
    ((X + X * sv % 2 ^ 64 * s) / 2 ^ 64 * 2 ^ 64) % s = X % s := by
  have hd : (X + X * sv % 2 ^ 64 * s) % 2 ^ 64 = 0 := by
    have h64 : 2 ^ 64 ∣ s * sv + 1 := Nat.dvd_of_mod_eq_zero hinv
    have hq := Nat.div_add_mod (X * sv) (2 ^ 64)
    have : X + X * sv % 2 ^ 64 * s + 2 ^ 64 * (X * sv / 2 ^ 64) * s = X * (s * sv + 1) := by
      rw [Nat.add_assoc, ← Nat.add_mul, Nat.add_comm (X * sv % 2 ^ 64), hq, Nat.mul_add, Nat.mul_one,
        Nat.add_comm, Nat.mul_assoc, Nat.mul_comm sv s]
    have h2 : 2 ^ 64 ∣ X + X * sv % 2 ^ 64 * s + 2 ^ 64 * (X * sv / 2 ^ 64) * s := by
      rw [this]; exact Nat.dvd_mul_left_of_dvd h64 X
    have h3 : 2 ^ 64 ∣ 2 ^ 64 * (X * sv / 2 ^ 64) * s := Nat.dvd_mul_right_of_dvd (Nat.dvd_mul_right _ _) _
    exact Nat.mod_eq_zero_of_dvd ((Nat.dvd_add_right h3).mp (by rwa [Nat.add_comm] at h2))
  have hu : X * sv % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hexact : (X + X * sv % 2 ^ 64 * s) / 2 ^ 64 * 2 ^ 64 = X + X * sv % 2 ^ 64 * s := by
    have := Nat.div_add_mod (X + X * sv % 2 ^ 64 * s) (2 ^ 64)
    rw [hd, Nat.add_zero, Nat.mul_comm] at this; exact this
  refine ⟨hd, ?_, ?_⟩
  · have hus : X * sv % 2 ^ 64 * s < 2 ^ 64 * s := Nat.mul_lt_mul_of_pos_right hu (by
      rcases Nat.eq_zero_or_pos s with h | h
      · rw [h, Nat.zero_mul] at hX; omega
      · exact h)
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    rw [Nat.mul_comm s (2 ^ 64)] at hX
    calc X + X * sv % 2 ^ 64 * s < 2 ^ 64 * s + 2 ^ 64 * s := Nat.add_lt_add hX hus
      _ = 2 * s * 2 ^ 64 := by rw [← Nat.two_mul, Nat.mul_comm (2 ^ 64) s, ← Nat.mul_assoc]
  · rw [hexact, Nat.add_mul_mod_self_right]

/-- One whole-word reduction extends the candidate-prefix congruence. -/
theorem trial_word64 {s acc r x V j : Nat}
    (step : r * 2 ^ 64 % s = (x + acc) % s)
    (prefixValue : acc * 2 ^ (64 * j) % s = V % s) :
    r * 2 ^ (64 * (j + 1)) % s = (V + 2 ^ (64 * j) * x) % s := by
  have shift : r * 2 ^ (64 * (j + 1)) = r * 2 ^ 64 * 2 ^ (64 * j) := by
    rw [Nat.mul_assoc, ← Nat.pow_add]
    congr 2
    omega
  rw [shift, ← Nat.mod_mul_mod, step, Nat.mod_mul_mod, Nat.add_mul]
  rw [Nat.add_mod, prefixValue, ← Nat.add_mod, Nat.add_comm, Nat.mul_comm x]

end VG.Proof.RsaKeyGen
