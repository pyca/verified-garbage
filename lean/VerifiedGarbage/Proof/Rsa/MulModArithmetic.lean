module

public import VerifiedGarbage.Proof.Framework.Omega

/-! # Arithmetic for binary modular multiplication -/

@[expose] public section
namespace VG.Proof.Rsa

/-- A sum below `2 m` modulo `m`. -/
theorem mod_of_lt_two {x M : Nat} (h : x < 2 * M) : x % M = if x < M then x else x - M := by
  split
  · exact Nat.mod_eq_of_lt (by assumption)
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The arithmetic of `addMod`: the negation of `b`, the sum, and the difference with `m`. -/
theorem addMod_impl {P A Bv M N1 β1 T β2 U β3 : Nat} (hA : A < M) (hB : Bv < M) (hM : 2 * M ≤ P)
    (h1 : N1 + Bv = 0 + P * β1) (_hN1 : N1 < P) (hβ1 : β1 ≤ 1)
    (h2 : T + N1 = A + P * β2) (hT : T < P) (hβ2 : β2 ≤ 1)
    (h3 : U + M = T + P * β3) (hU : U < P) (hβ3 : β3 ≤ 1) :
    (if β3 = 0 then U else T) = (A + Bv) % M := by
  rw [mod_of_lt_two (by omega)]
  rcases (by omega : β1 = 0 ∨ β1 = 1) with rfl | rfl <;>
  rcases (by omega : β2 = 0 ∨ β2 = 1) with rfl | rfl <;>
  rcases (by omega : β3 = 0 ∨ β3 = 1) with rfl | rfl <;>
  simp only [Nat.mul_zero, Nat.mul_one] at h1 h2 h3 <;> split <;> split <;> omega

/-- One step's arithmetic. -/
theorem mulMod_arith {A0 X0 Y0 M i : Nat} :
    ((A0 + Y0 % 2 ^ i * X0) % M + (Y0 / 2 ^ i) % 2 * (2 ^ i * X0 % M)) % M =
      (A0 + Y0 % 2 ^ (i + 1) * X0) % M := by
  have e : Y0 % 2 ^ (i + 1) = Y0 % 2 ^ i + 2 ^ i * ((Y0 / 2 ^ i) % 2) := by
    rw [Nat.pow_succ, Nat.mod_mul, Nat.mul_comm]
  rw [e, Nat.add_mul, ← Nat.add_assoc, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod,
    Nat.add_mod (A0 + Y0 % 2 ^ i * X0), Nat.mul_mod ((Y0 / 2 ^ i) % 2), Nat.mod_mod, ← Nat.mul_mod,
    ← Nat.add_mod]
  congr 1
  rw [Nat.mul_comm (2 ^ i)]
  ac_rfl

theorem double_arith {X0 M i : Nat} : (2 ^ i * X0 % M + 2 ^ i * X0 % M) % M = 2 ^ (i + 1) * X0 % M := by
  rw [← Nat.add_mod, ← Nat.two_mul, Nat.pow_succ, Nat.mul_comm (2 ^ i) 2, Nat.mul_assoc]

end VG.Proof.Rsa
