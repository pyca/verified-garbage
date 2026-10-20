module
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp


/-! # A borrow-masked addition implements modular subtraction -/

@[expose] public section

namespace VG.Proof.Bignum.Arm

theorem subMod_value {A B M R D c : Nat} (ha : A < M) (hb : B < M)
    (hm : M < R) (hd : D < R) (hc : c ≤ 1) (value : D + B = A + R * c) :
    (D + c * M) % R = (A + M - B) % M ∧ (D + c * M) % R < M := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hc with rfl | rfl
  · simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero] at value ⊢
    have hdm : D < M := by omega
    have eq : A + M - B = D + M := by omega
    simp only [Nat.mod_eq_of_lt hd, eq, Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt hdm]
    exact ⟨trivial, hdm⟩
  · simp only [Nat.mul_one, Nat.one_mul] at value ⊢
    have order : A < B := by omega
    have small : A + M - B < M := by omega
    have eq : D + M = R + (A + M - B) := by omega
    simp only [eq, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega : A + M - B < R),
      Nat.mod_eq_of_lt small]
    exact ⟨trivial, small⟩

end VG.Proof.Bignum.Arm
