module

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! # A column's carry, from its sums

For a column `V = 2³² H + L + c` (the products' high words `H`, their low
words `L` and the incoming carry `c`, with `L + c < 2⁶⁴`), the word
`Z_hi` of `V mod 2⁶⁴` and the comparison `Z_hi < H mod 2³²` give the
outgoing carry `V / 2³²` (`carry_eq`). The quotient digit cancels the
column's low word (`cancel_digit`).
-/

@[expose] public section

namespace VG.Proof.Mont.X86.Sse2

theorem carry_eq (H L c : Nat) (hL : L + c < 2 ^ 64) (hV : (2 ^ 32 * H + L + c) / 2 ^ 32 < 2 ^ 64) :
    (2 ^ 32 * H + L + c) % 2 ^ 64 / 2 ^ 32 + 2 ^ 32 * ((H / 2 ^ 32 +
      (decide ((2 ^ 32 * H + L + c) % 2 ^ 64 / 2 ^ 32 < H % 2 ^ 32)).toNat) % 2 ^ 32) =
      (2 ^ 32 * H + L + c) / 2 ^ 32 := by
  have e1 : (2 ^ 32 * H + L + c) / 2 ^ 32 = H + (L + c) / 2 ^ 32 := by omega
  have e2 : (2 ^ 32 * H + L + c) % 2 ^ 64 / 2 ^ 32 = (H + (L + c) / 2 ^ 32) % 2 ^ 32 := by
    rw [show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 by decide, Nat.mod_mul_right_div_self, e1]
  have hu : (L + c) / 2 ^ 32 < 2 ^ 32 := by omega
  rw [e1] at hV ⊢
  rw [e2]
  by_cases h : (H + (L + c) / 2 ^ 32) % 2 ^ 32 < H % 2 ^ 32
  · simp only [h, decide_true, Bool.toNat_true]; omega
  · simp only [h, decide_false, Bool.toNat_false]; omega

/-- `carry_eq` for the column's sum `P` and high words' sum `H`. -/
theorem col_carry {P H c Zh : Nat} (hle : 2 ^ 32 * H ≤ P) (hL : P - 2 ^ 32 * H + c < 2 ^ 64)
    (hV : (P + c) / 2 ^ 32 < 2 ^ 64) (hZ : Zh = (P + c) % 2 ^ 64 / 2 ^ 32) :
    Zh + 2 ^ 32 * ((H / 2 ^ 32 + (decide (Zh < H % 2 ^ 32)).toNat) % 2 ^ 32) = (P + c) / 2 ^ 32 := by
  have e : 2 ^ 32 * H + (P - 2 ^ 32 * H) + c = P + c := by omega
  have := carry_eq H (P - 2 ^ 32 * H) c hL (by rw [e]; exact hV)
  rw [e] at this
  rw [hZ]; exact this

/-- The quotient digit `q = x (-m⁻¹) mod r` cancels `x`'s low word. -/
theorem cancel_digit (r x m i : Nat) (hi : (m * i + 1) % r = 0) : (x + ((x % r * i) % r) * m) % r = 0 := by
  rw [Nat.add_mod, Nat.mod_mul_mod, Nat.add_mod_mod]
  have e : x % r + (x % r * i) * m = (x % r) * (m * i + 1) := by grind
  rw [e, Nat.mul_mod, hi, Nat.mul_zero, Nat.zero_mod]

/-- Two words of a number below `2⁶⁴`. -/
theorem words_split {x y h : Nat} (hx : x < 2 ^ 32) (e : x + 2 ^ 32 * y = h) : x = h % 2 ^ 32 ∧ y = h / 2 ^ 32 := by
  omega

/-- The bounds of a column with its quotient digit's product `qm`: no sum
overflows, and the next carry is again at most `(2 N + 2) 2³²`. -/
theorem column_bounds {AB QM H c qm N : Nat} (hN : N < 2 ^ 29) (hP : AB ≤ N * (2 ^ 32 - 1) * (2 ^ 32 - 1))
    (hQ : QM ≤ N * (2 ^ 32 - 1) * (2 ^ 32 - 1)) (fl : 2 ^ 32 * H ≤ AB + QM)
    (fw : AB + QM - 2 ^ 32 * H ≤ (2 * N + 1) * (2 ^ 32 - 1)) (hc : c ≤ (2 * N + 2) * 2 ^ 32)
    (hqm : qm ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1)) :
    H + qm / 2 ^ 32 < 2 ^ 64 ∧ 2 ^ 32 * (H + qm / 2 ^ 32) ≤ AB + QM + qm ∧
      AB + QM + qm - 2 ^ 32 * (H + qm / 2 ^ 32) + c < 2 ^ 64 ∧ (AB + QM + qm + c) / 2 ^ 32 < 2 ^ 64 ∧
      (AB + QM + qm + c) / 2 ^ 32 ≤ (2 * N + 2) * 2 ^ 32 := by
  have := Nat.div_add_mod qm (2 ^ 32)
  have := Nat.mod_lt qm (show 0 < 2 ^ 32 by decide)
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- A column sum without a digit (`qm = 0`). -/
theorem column_bounds0 {AB QM H c N : Nat} (hN : N < 2 ^ 29) (hP : AB ≤ N * (2 ^ 32 - 1) * (2 ^ 32 - 1))
    (hQ : QM ≤ N * (2 ^ 32 - 1) * (2 ^ 32 - 1)) (fl : 2 ^ 32 * H ≤ AB + QM)
    (fw : AB + QM - 2 ^ 32 * H ≤ (2 * N + 1) * (2 ^ 32 - 1)) (hc : c ≤ (2 * N + 2) * 2 ^ 32) :
    H < 2 ^ 64 ∧ AB + QM - 2 ^ 32 * H + c < 2 ^ 64 ∧ (AB + QM + c) / 2 ^ 32 < 2 ^ 64 ∧
      (AB + QM + c) / 2 ^ 32 ≤ (2 * N + 2) * 2 ^ 32 := by
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- After the columns: `R (T + R c) = A B + Q M` with `A, Q < R` and `B < M ≤ R`
puts `T + R c` below `2 M`, and `c` below 2. -/
theorem final_bound {R A B M Q T c : Nat} (alt : A < R) (blt : B < M) (mle : M ≤ R) (qlt : Q < R)
    (eq : R * (T + R * c) = A * B + Q * M) : T + R * c < 2 * M ∧ c < 2 := by
  have rpos : 0 < R := by omega
  have a : A * B < R * M := Nat.mul_lt_mul_of_lt_of_le alt (Nat.le_of_lt blt) (by omega)
  have q : Q * M ≤ R * M := Nat.mul_le_mul_right _ (Nat.le_of_lt qlt)
  have bound : R * (T + R * c) < R * (2 * M) := by
    rw [eq, show R * (2 * M) = R * M + R * M by rw [Nat.two_mul, Nat.mul_add]]; omega
  have tlt := (Nat.mul_lt_mul_left rpos).mp bound
  refine ⟨tlt, ?_⟩
  have : R * c < R * 2 := by
    have : R * c ≤ T + R * c := Nat.le_add_left _ _
    have : 2 * M ≤ R * 2 := by rw [Nat.mul_comm R]; omega
    omega
  exact (Nat.mul_lt_mul_left rpos).mp this

/-- The result `O = (T + R c) mod M` is `A B R⁻¹` modulo `M`. -/
theorem final_mod {R A B M Q X : Nat} (eq : R * X = A * B + Q * M) : X % M * R % M = A * B % M := by
  rw [Nat.mod_mul_mod, Nat.mul_comm, eq, Nat.add_mul_mod_self_right]

end VG.Proof.Mont.X86.Sse2
