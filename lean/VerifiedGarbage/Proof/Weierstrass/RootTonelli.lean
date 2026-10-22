module

public import VerifiedGarbage.Impl.EcKey.Compressed.Root
public import VerifiedGarbage.Proof.Weierstrass.Law
import VerifiedGarbage.Proof.Weierstrass.Sqrt
import VerifiedGarbage.Proof.Weierstrass.RootPowers

/-! # Correctness of the two-adic square-root descent

The invariant is `r² = a t`, with `t^(2^n) = 1` and
`c^(2^n) = -1`. Each round halves the bound on the order of `t`.
All field facts come from the existing curve-law interface.
-/

@[expose] public section

namespace VG.Proof.Weierstrass

open Spec.Weierstrass VG.Impl.EcKey.Compressed

variable {C : Curve}

/-- The fixed-round machine implementation may run the descent on zero;
its accumulator stays zero in every round. -/
theorem rootDescent_zero (n : Nat) (t c : Fe C) : rootDescent n 0 t c = 0 := by
  induction n generalizing t c with
  | zero => rfl
  | succ n ih =>
    simp only [rootDescent, Fin.zero_mul]
    exact ih _ _

/-- Removing the early return for zero does not change the candidate.
The assembly runs the same number of descent rounds for every input. -/
theorem rootTonelli_eq_descent (a z : Fe C) (q s : Nat) (hq : 0 < q) :
    rootTonelli a q s z = rootDescent (s - 1) (pow a ((q + 1) / 2)) (pow a q) (pow z q) := by
  unfold rootTonelli
  split
  next ha =>
    subst a
    have he : 0 < (q + 1) / 2 := by omega
    have hzero : pow (0 : Fe C) ((q + 1) / 2) = 0 := by
      rw [pow_eq_npow]
      obtain ⟨k, hk⟩ : ∃ k, (q + 1) / 2 = k + 1 := ⟨(q + 1) / 2 - 1, by omega⟩
      rw [hk, Lean.Grind.Semiring.pow_succ]
      grind
    rw [hzero, rootDescent_zero]
  · rfl

theorem rootDescent_square (hL : Law C) (n : Nat) (r t c a : Fe C)
    (ht : t ^ (2 ^ n) = 1) (hc : c ^ (2 ^ n) = -1)
    (hr : r ^ 2 = a * t) : rootDescent n r t c ^ 2 = a := by
  induction n generalizing r t c with
  | zero =>
    simp only [Nat.pow_zero, Lean.Grind.Semiring.pow_one] at ht
    simpa only [rootDescent, ht, Lean.Grind.Semiring.mul_one] using hr
  | succ n ih =>
    have he : 2 * 2 ^ n = 2 ^ (n + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    have hc' : (c * c) ^ (2 ^ n) = -1 := by
      rw [← Lean.Grind.Semiring.pow_two, pow_mul_exponents, he]
      exact hc
    rw [rootDescent]
    split
    next hb =>
      rw [pow_eq_npow] at hb
      simp only [Lean.Grind.Semiring.mul_one]
      exact ih r t (c * c) hb hc' hr
    next hb =>
      have hu : (t ^ (2 ^ n)) ^ 2 = 1 := by
        rw [pow_mul_exponents, Nat.mul_comm (2 ^ n) 2, he]
        exact ht
      have hne : t ^ (2 ^ n) ≠ 1 := by simpa only [pow_eq_npow] using hb
      have hprod : t ^ (2 ^ n) * t ^ (2 ^ n) = (1 : Fe C) * 1 := by
        rw [← Lean.Grind.Semiring.pow_two, hu]
        grind
      have hu' : t ^ (2 ^ n) = -1 := (square_roots_eq_or_neg hL hprod).resolve_left hne
      apply ih (r * c) (t * (c * c)) (c * c)
      · rw [mul_pow_exponent, hu', hc']
        grind
      · exact hc'
      · rw [mul_pow_exponent, hr, Lean.Grind.Semiring.pow_two]
        grind

/-- Every square has a candidate; `hc` is the kernel-checked nonresidue
certificate for the curve's chosen `z`. Zero is included. -/
theorem rootTonelli_square (hL : Law C) (hp3 : 2 < C.p) (q s : Nat) (z a : Fe C)
    (hs : 0 < s) (hq : q % 2 = 1) (hp : C.p - 1 = q * 2 ^ s)
    (hc : pow z (q * 2 ^ (s - 1)) = -1)
    (ha : ∃ y : Fe C, y * y = a) :
    rootTonelli a q s z * rootTonelli a q s z = a := by
  by_cases hzero : a = 0
  · simp only [rootTonelli, hzero, ↓reduceIte, Fin.mul_zero]
  · simp only [rootTonelli, hzero, ↓reduceIte]
    rw [← Lean.Grind.Semiring.pow_two]
    apply rootDescent_square hL
    · rcases ha with ⟨y, hy⟩
      have hy0 : y ≠ 0 := by intro h; apply hzero; rw [← hy, h]; grind
      have he : 2 * 2 ^ (s - 1) = 2 ^ s := by
        calc
          2 * 2 ^ (s - 1) = 2 ^ (s - 1) * 2 := Nat.mul_comm _ _
          _ = 2 ^ (s - 1 + 1) := (Nat.pow_succ _ _).symm
          _ = 2 ^ s := by rw [Nat.sub_add_cancel hs]
      have he' : 2 * (q * 2 ^ (s - 1)) = C.p - 1 := by
        rw [← Nat.mul_assoc, Nat.mul_comm 2 q, Nat.mul_assoc, he, hp]
      rw [pow_eq_npow, pow_mul_exponents, ← hy, ← Lean.Grind.Semiring.pow_two,
        pow_mul_exponents, he']
      exact root_fermat hL hp3 y hy0
    · rw [pow_eq_npow, pow_mul_exponents]
      simpa only [pow_eq_npow] using hc
    · rw [pow_eq_npow, pow_eq_npow, pow_mul_exponents,
        show (q + 1) / 2 * 2 = q + 1 by omega, Lean.Grind.Semiring.pow_succ]
      grind

end VG.Proof.Weierstrass
