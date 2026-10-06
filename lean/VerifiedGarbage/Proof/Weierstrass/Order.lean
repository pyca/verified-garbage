import VerifiedGarbage.Proof.Weierstrass.Law

/-!
# The order of `G`, by the kernel

`ladRep C P k nb i` is the ladder's representative of `[k >>> (nb - i)]P`
after `i` of the `nb` bits of `k` from the top, by the complete formulas
(`ladRep_rep`, from `Law.step`); for `k < 2^nb`, after all of them, of
`[k]P`. Its `Z` is zero exactly for `O`, so the kernel's evaluation of
`ladRep` for `k = n` gives `[n]G = O` (`mul_n_of_ladRep`): with `n` prime,
`G` has order `n`, which the comb's Jacobian additions need
(`Proof/Weierstrass/Booth.lean`).
-/

namespace VG.Proof.Weierstrass

open Spec.Weierstrass

variable {C : Curve}

/-- The ladder's representative after `i` of the `nb` bits of `k`, from the
top: a doubling, then an addition of `P` kept for a set bit. -/
def ladRep (C : Curve) (Px Py Pz : Fe C) (k nb : Nat) : Nat → Fe C × Fe C × Fe C
  | 0 => (0, 1, 0)
  | i + 1 =>
    let r := ladRep C Px Py Pz k nb i
    let d := rcbAdd (Fin.ofNat C.p C.a) (Fin.ofNat C.p (3 * C.b)) r.1 r.2.1 r.2.2 r.1 r.2.1 r.2.2
    let t := rcbAdd (Fin.ofNat C.p C.a) (Fin.ofNat C.p (3 * C.b)) d.1 d.2.1 d.2.2 Px Py Pz
    if k.testBit (nb - (i + 1)) then t else d

theorem ladRep_rep (hC : Law C) {P : Point C} (hP : onCurve C P = true) {Px Py Pz : Fe C}
    (hPr : Rep C Px Py Pz P) {k nb : Nat} (hk : k < 2 ^ nb) :
    ∀ i ≤ nb, Rep C (ladRep C Px Py Pz k nb i).1 (ladRep C Px Py Pz k nb i).2.1
      (ladRep C Px Py Pz k nb i).2.2 (mul (k >>> (nb - i)) P)
  | 0, _ => by
    rw [Nat.sub_zero, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hk,
      show mul 0 P = .infinity by rw [Spec.Weierstrass.mul]; simp]
    exact ⟨rfl, hC.one_ne_zero, rfl⟩
  | i + 1, hi => by
    have ih := ladRep_rep hC hP hPr hk i (by omega)
    have e : nb - i = nb - (i + 1) + 1 := by omega
    rw [e] at ih
    have h := hC.step hP hPr ih rfl rfl
    by_cases hb : k.testBit (nb - (i + 1))
    · simp only [hb, ↓reduceIte] at h
      simp only [ladRep, hb, ↓reduceIte]
      exact h
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
      simp only [ladRep, hb, Bool.false_eq_true, ↓reduceIte]
      exact h

/-- `[n]G = O`, from the ladder's `Z` for `n`. -/
theorem mul_n_of_ladRep (hC : Law C) (hG : onCurve C (G C) = true) {nb : Nat}
    (hk : C.n < 2 ^ nb)
    (hz : (ladRep C (Fin.ofNat C.p C.gx) (Fin.ofNat C.p C.gy) 1 C.n nb nb).2.2 = 0) :
    mul C.n (G C) = .infinity := by
  have h := ladRep_rep hC hG (Px := Fin.ofNat C.p C.gx) (Py := Fin.ofNat C.p C.gy) (Pz := 1)
    ⟨hC.one_ne_zero, (Lean.Grind.Semiring.mul_one _).symm, (Lean.Grind.Semiring.mul_one _).symm⟩
    hk nb (Nat.le_refl _)
  rw [Nat.sub_self, Nat.shiftRight_zero] at h
  exact (h.z_eq_zero_iff).mp hz

end VG.Proof.Weierstrass
