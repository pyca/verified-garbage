module

public import VerifiedGarbage.Proof.Rsa.KeyMath
public import VerifiedGarbage.Proof.Framework.Omega

/-! # Native-word arithmetic for binary modular inversion -/

@[expose] public section
namespace VG.Proof.Rsa
theorem subMod_impl {P M a b t1 β t4 e β' : Nat} (hM : M ≤ P) (hb : b < M)
    (h1 : t1 + b = a + P * β) (ht1 : t1 < P) (hβ : β ≤ 1) (h4 : t4 = if β = 0 then 0 else P - M)
    (h2 : e + t4 = t1 + P * β') (he : e < P) (hβ' : β' ≤ 1) : e = subMod M a b := by
  unfold subMod
  rcases (by omega : β = 0 ∨ β = 1) with rfl | rfl <;>
  rcases (by omega : β' = 0 ∨ β' = 1) with rfl | rfl <;>
  split at h4 <;> split <;> omega

theorem halfMod_impl {P M X t4 y β c : Nat} (hM : M ≤ P) (hX : X < P)
    (h4 : t4 = if X % 2 = 0 then 0 else P - M) (h3 : y + t4 = X + P * β) (hy : y < P) (hβ : β ≤ 1)
    (hc : c = (β + X % 2) % 2) : (y + P * c) / 2 = halfMod M X := by
  unfold halfMod
  rcases (by omega : β = 0 ∨ β = 1) with rfl | rfl <;>
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;>
  split at h4 <;> split <;> omega

theorem invU_arith {u v x₁ x₂ β₁ β₂ P : Nat} (d₁ : x₁ + v = u + P * β₁) (b₁ : β₁ ≤ 1) (l₁ : x₁ < P)
    (d₂ : x₂ + u = v + P * β₂) (b₂ : β₂ ≤ 1) (l₂ : x₂ < P) :
    (if u % 2 = 0 then u else if (if u % 2 = 1 ∧ u < v then 1 else 0) = 0 then x₁ else x₂) / 2 =
      (if u % 2 = 1 then (if u < v then (v - u) / 2 else (u - v) / 2) else u / 2) := by
  rcases (by omega : β₁ = 0 ∨ β₁ = 1) with rfl | rfl <;> rcases (by omega : β₂ = 0 ∨ β₂ = 1) with rfl | rfl <;>
  simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] at d₁ d₂ <;>
  by_cases e : u % 2 = 1 <;> by_cases f : u < v <;>
  simp only [e, f, and_true, and_false, ↓reduceIte, show u % 2 = 0 ↔ ¬ u % 2 = 1 by omega, not_false_eq_true,
    Nat.one_ne_zero] <;> omega

theorem borrow_iff {x a b P β : Nat} (hv : x + b = a + P * β) (hx : x < P) (hβ : β ≤ 1) :
    β = 0 ↔ b ≤ a := by
  rcases (by omega : β = 0 ∨ β = 1) with rfl | rfl <;> simp only [Nat.mul_zero, Nat.mul_one] at hv <;> omega

theorem invStep_arith {u v x₁ x₂ M : Nat} :
    (if u % 2 = 1 then (if u < v then (v - u) / 2 else (u - v) / 2) else u / 2,
     (if u % 2 = 1 ∧ u < v then u else v),
     halfMod M (if (u % 2) = 0 then x₁ else
       if (if u % 2 = 1 ∧ u < v then 1 else 0) = 0 then subMod M x₁ x₂ else subMod M x₂ x₁),
     (if (if u % 2 = 1 ∧ u < v then 1 else 0) = 0 then x₂ else x₁)) =
    VG.Proof.Rsa.invStep M (u, v, x₁, x₂) := by
  unfold VG.Proof.Rsa.invStep
  by_cases e : u % 2 = 1 <;> by_cases f : u < v <;>
  simp [e, f, show u % 2 = 0 ↔ ¬ u % 2 = 1 by omega]

theorem invI_start' {a m : Nat} (hm : m % 2 = 1) (h1 : 1 < m) : InvI a m (a, m, 1, 0) :=
  ⟨hm, h1, show 0 < m by omega, ⟨0, by simp⟩, by simp, rfl⟩

end VG.Proof.Rsa
