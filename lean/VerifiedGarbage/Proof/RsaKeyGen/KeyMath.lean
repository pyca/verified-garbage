import VerifiedGarbage.Proof.Rsa.KeyMath
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Spec.RsaKeyGen
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# An RSA key from its primes: the arithmetic

What `vg_rsa_keygen_key`'s steps compute:

* `halveIter`: halving `(u, v, f)` while `u` and `v` are both even, from
  `(a, b, a b)`, ends with `lcm(a, b) = f / gcd(u, v)`, and `u` and `v` not
  both even unless both are zero (`halve_lcm`, `halve_end`);
* the inverse of the specification, `Rsa.inverse e L`, by `e`: none for
  `e = 0`, 1 for `e = 1` but `L = 1`, `Q t + (1 + R t) / e` for an odd `e`
  (`L = e Q + R`, `t = e − x`, `x = R⁻¹ mod e`), and `(e mod L)⁻¹ mod L` for
  an even one (`inverse_zero`, `inverse_one`, `inverse_odd`,
  `inverse_even`).
-/

namespace VG.Proof.RsaKeyGen

open VG.Proof.Rsa (inverse_eq inverse_none)

/-! ## The halving -/

/-- One step: `(u, v, f)` halved if `u` and `v` are both even. -/
def halveStep (st : Nat × Nat × Nat) : Nat × Nat × Nat :=
  if st.1 % 2 = 0 ∧ st.2.1 % 2 = 0 then (st.1 / 2, st.2.1 / 2, st.2.2 / 2) else st

/-- `k` steps. -/
def halveIter : Nat → Nat × Nat × Nat → Nat × Nat × Nat
  | 0, st => st
  | k + 1, st => halveIter k (halveStep st)

theorem halveIter_succ (k : Nat) (st : Nat × Nat × Nat) : halveIter (k + 1) st = halveIter k (halveStep st) := rfl

/-- The last step of `k + 1`. -/
theorem halveIter_succ' : ∀ (k : Nat) (st : Nat × Nat × Nat), halveIter (k + 1) st = halveStep (halveIter k st)
  | 0, _ => rfl
  | k + 1, st => by rw [halveIter_succ, halveIter_succ' k, ← halveIter_succ]

/-- A state not both even stays. -/
theorem halveIter_stuck {st : Nat × Nat × Nat} (h : ¬ (st.1 % 2 = 0 ∧ st.2.1 % 2 = 0)) :
    ∀ k, halveIter k st = st := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [halveIter_succ, halveStep, ite_eq_right_of_eq_false _ _ (eq_false h), ih]

/-- If the end is both even, every step halved. -/
theorem halveIter_all : ∀ (k : Nat) (st : Nat × Nat × Nat),
    (halveIter k st).1 % 2 = 0 → (halveIter k st).2.1 % 2 = 0 →
    st.1 = 2 ^ k * (halveIter k st).1 ∧ st.2.1 = 2 ^ k * (halveIter k st).2.1
  | 0, _, _, _ => by simp [halveIter]
  | k + 1, st, h1, h2 => by
    rw [halveIter_succ] at h1 h2 ⊢
    by_cases hb : st.1 % 2 = 0 ∧ st.2.1 % 2 = 0
    · have e : halveStep st = (st.1 / 2, st.2.1 / 2, st.2.2 / 2) := ite_eq_left_of_eq_true _ _ (eq_true hb)
      rw [e] at h1 h2 ⊢
      have ih := halveIter_all k _ h1 h2
      generalize halveIter k (st.1 / 2, st.2.1 / 2, st.2.2 / 2) = s at ih ⊢
      dsimp only at ih
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc, Nat.mul_assoc, ← ih.1, ← ih.2]
      omega
    · have e : halveStep st = st := ite_eq_right_of_eq_false _ _ (eq_false hb)
      rw [e, halveIter_stuck hb] at h1 h2
      exact absurd ⟨h1, h2⟩ hb

/-- At the end of `K` steps from numbers below `2^K`, `u` and `v` are not
both even unless both are zero. -/
theorem halve_end {a b K : Nat} (ha : a < 2 ^ K) (hb : b < 2 ^ K) (f : Nat) :
    let st := halveIter K (a, b, f)
    st.1 % 2 = 1 ∨ st.2.1 % 2 = 1 ∨ (st.1 = 0 ∧ st.2.1 = 0) := by
  dsimp only
  have hall := halveIter_all K (a, b, f)
  generalize halveIter K (a, b, f) = s at hall ⊢
  obtain ⟨u, v, g⟩ := s
  dsimp only at hall ⊢
  by_cases h1 : u % 2 = 0
  · by_cases h2 : v % 2 = 0
    · obtain ⟨e1, e2⟩ := hall h1 h2
      refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · rcases Nat.eq_zero_or_pos u with h | h
        · exact h
        · have : 2 ^ K ≤ 2 ^ K * u := Nat.le_mul_of_pos_right _ h
          omega
      · rcases Nat.eq_zero_or_pos v with h | h
        · exact h
        · have : 2 ^ K ≤ 2 ^ K * v := Nat.le_mul_of_pos_right _ h
          omega
    · exact Or.inr (Or.inl (by omega))
  · exact Or.inl (by omega)

/-- What the halving keeps: `a = 2^k u`, `b = 2^k v` and `f = 2^k u v`. -/
def HalveI (a b : Nat) (st : Nat × Nat × Nat) : Prop :=
  ∃ k, a = 2 ^ k * st.1 ∧ b = 2 ^ k * st.2.1 ∧ st.2.2 = 2 ^ k * st.1 * st.2.1

theorem halveStep_inv {a b : Nat} {st : Nat × Nat × Nat} (h : HalveI a b st) : HalveI a b (halveStep st) := by
  obtain ⟨u, v, f⟩ := st
  obtain ⟨k, ha, hb, hf⟩ := h
  dsimp only at ha hb hf
  by_cases hev : u % 2 = 0 ∧ v % 2 = 0
  · rw [halveStep, ite_eq_left_of_eq_true _ _ (eq_true hev)]
    obtain ⟨u', rfl⟩ : ∃ u', u = 2 * u' := ⟨u / 2, by omega⟩
    obtain ⟨v', rfl⟩ : ∃ v', v = 2 * v' := ⟨v / 2, by omega⟩
    have h2 : 0 < 2 := by decide
    refine ⟨k + 1, ?_, ?_, ?_⟩ <;> dsimp only <;>
      simp only [Nat.mul_div_cancel_left _ h2]
    · rw [ha, Nat.pow_succ, Nat.mul_assoc]
    · rw [hb, Nat.pow_succ, Nat.mul_assoc]
    · rw [hf, show 2 ^ k * (2 * u') * (2 * v') = 2 * (2 ^ (k + 1) * u' * v') by
        rw [Nat.pow_succ]; grind, Nat.mul_div_cancel_left _ h2]
  · rw [halveStep, ite_eq_right_of_eq_false _ _ (eq_false hev)]
    exact ⟨k, ha, hb, hf⟩

theorem halveIter_inv {a b : Nat} : ∀ (k : Nat) {st : Nat × Nat × Nat}, HalveI a b st → HalveI a b (halveIter k st)
  | 0, _, h => h
  | k + 1, _, h => halveIter_inv k (halveStep_inv h)

/-- `lcm(a, b) = f / gcd(u, v)` after any number of steps from `(a, b, a b)`. -/
theorem halve_lcm (a b k : Nat) :
    let st := halveIter k (a, b, a * b)
    Nat.lcm a b = st.2.2 / Nat.gcd st.1 st.2.1 := by
  dsimp only
  have hI := halveIter_inv k (a := a) (b := b) (st := (a, b, a * b)) ⟨0, by simp, by simp, by simp⟩
  generalize halveIter k (a, b, a * b) = s at hI ⊢
  obtain ⟨u, v, f⟩ := s
  obtain ⟨j, ha, hb, hf⟩ := hI
  dsimp only at ha hb hf ⊢
  subst ha hb hf
  rw [Nat.lcm_mul_left, Nat.lcm, Nat.mul_assoc,
    Nat.mul_div_assoc _ (Nat.dvd_trans (Nat.gcd_dvd_left u v) (Nat.dvd_mul_right u v))]

/-- The halving's `f` is zero when `u` and `v` are. -/
theorem halve_zero (a b k : Nat) :
    let st := halveIter k (a, b, a * b)
    st.1 = 0 → st.2.1 = 0 → st.2.2 = 0 := by
  dsimp only
  intro h1 h2
  obtain ⟨j, -, -, hf⟩ := halveIter_inv k (a := a) (b := b) (st := (a, b, a * b)) ⟨0, by simp, by simp, by simp⟩
  rw [hf, h1]; simp

/-- After the halving and the swap (`v` odd if one is): `lcm(a, b) = f / g`
with `g` 1 for `v ≤ 1` and `gcd(u, v)` otherwise. -/
theorem lcm_eq {a b K : Nat} (ha : a < 2 ^ K) (hb : b < 2 ^ K) :
    let st := halveIter K (a, b, a * b)
    let u := if st.2.1 % 2 = 0 then st.2.1 else st.1
    let v := if st.2.1 % 2 = 0 then st.1 else st.2.1
    (2 ≤ v → v % 2 = 1) ∧ Nat.lcm a b = st.2.2 / (if v ≤ 1 then 1 else Nat.gcd u v) := by
  have he := halve_end ha hb (a * b)
  have hl := halve_lcm a b K
  have hz := halve_zero a b K
  dsimp only at he hl hz ⊢
  generalize halveIter K (a, b, a * b) = s at he hl hz ⊢
  obtain ⟨x, y, f⟩ := s
  dsimp only at he hl hz ⊢
  rw [hl]
  by_cases hs : y % 2 = 0
  · simp only [hs, ↓reduceIte]
    rcases he with h | h | ⟨h1, h2⟩
    · refine ⟨fun _ => h, ?_⟩
      split
      · next hx =>
        have : x = 1 := by omega
        subst this; simp
      · rw [Nat.gcd_comm]
    · omega
    · subst h1 h2; simp [hz rfl rfl]
  · simp only [hs, ↓reduceIte]
    refine ⟨fun _ => by omega, ?_⟩
    split
    · next hy =>
      have : y = 1 := by omega
      subst this; simp
    · rfl

/-! ## The inverse of the specification -/

/-- What an inverse of the specification is: `a x ≡ 1 (mod m)`, and `x < m`
for `m > 0`. -/
theorem inverse_some {a m x : Nat} (h : Spec.Rsa.inverse a m = some x) : a * x % m = 1 ∧ (0 < m → x < m) := by
  unfold Spec.Rsa.inverse at h
  dsimp only at h
  split at h
  · rename_i h1
    cases h
    refine ⟨h1, fun hm => ?_⟩
    have := Int.emod_lt_of_pos (Spec.Rsa.xgcd (a % m) 1 m 0).2 (by omega : (0 : Int) < m)
    have := Int.emod_nonneg (Spec.Rsa.xgcd (a % m) 1 m 0).2 (by omega : (m : Int) ≠ 0)
    omega
  · cases h

/-- Modulo 0: the inverse of 1 only. -/
theorem inverse_mod_zero (a : Nat) : Spec.Rsa.inverse a 0 = if a = 1 then some 1 else none := by
  by_cases h : a = 1
  · subst h
    unfold Spec.Rsa.inverse
    rw [Spec.Rsa.xgcd]
    simp only [Nat.mod_zero, Nat.one_ne_zero, ↓reduceIte, Nat.zero_mod, Nat.zero_div, Nat.cast_zero, zero_mul,
      sub_zero]
    rw [Spec.Rsa.xgcd]
    simp
  · rw [ite_eq_right h]
    exact inverse_none (by rw [Nat.gcd_zero_right]; exact h)

/-- Modulo 1: none. -/
theorem inverse_mod_one (a : Nat) : Spec.Rsa.inverse a 1 = none := by
  unfold Spec.Rsa.inverse
  simp

/-- `e = 0`: none. -/
theorem inverse_zero (L : Nat) : Spec.Rsa.inverse 0 L = none := by
  rcases Nat.lt_or_ge L 2 with h | h
  · rcases (show L = 0 ∨ L = 1 by omega) with rfl | rfl
    · rw [inverse_mod_zero]; simp
    · exact inverse_mod_one 0
  · exact inverse_none (by rw [Nat.gcd_zero_left]; omega)

/-- `e = 1`: 1, but modulo 1. -/
theorem inverse_one (L : Nat) : Spec.Rsa.inverse 1 L = if L = 1 then none else some 1 := by
  rcases Nat.lt_or_ge L 2 with h | h
  · rcases (show L = 0 ∨ L = 1 by omega) with rfl | rfl
    · rw [inverse_mod_zero]; simp
    · rw [inverse_mod_one]; simp
  · rw [ite_eq_right (show L ≠ 1 by omega)]
    exact inverse_eq (by omega) (by omega) (by simp)

/-- An odd `e ≥ 3` below `2⁶⁴`: from `L = e Q + R` and `x = R⁻¹ mod e`
(`x R ≡ 1`, `x < e`), the inverse is `Q t + c` with `t = e − x` and
`c = (1 + R t) e⁻¹ mod 2⁶⁴`. -/
theorem inverse_odd {e L Q R x einv : Nat} (he3 : 3 ≤ e) (he64 : e < 2 ^ 64) (hL : 2 ≤ L)
    (hQR : L = e * Q + R) (hR : R < e) (hx : (e : Int) ∣ (x : Int) * R - 1) (hxe : x < e)
    (hinv : e * einv % 2 ^ 64 = 1) :
    Spec.Rsa.inverse e L =
      some (Q * (e - x) + ((R * (e - x) % 2 ^ 64 + 1) % 2 ^ 64 * einv) % 2 ^ 64) := by
  -- `x ≥ 1`, so `t = e − x < e`.
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · subst h
      obtain ⟨c, hc⟩ := hx
      simp at hc
      have := Int.eq_one_of_mul_eq_one_right (by omega)
        (show (e : Int) * (-c) = 1 by rw [Int.mul_neg, ← hc, Int.neg_neg])
      omega
    · exact h
  generalize ht : e - x = t
  have hte : t < e := by omega
  -- `1 + R t ≡ 0 (mod e)`.
  have hdv : e ∣ 1 + R * t := by
    have : ((1 + R * t : Nat) : Int) = (e : Int) * R - ((x : Int) * R - 1) := by
      rw [← ht]; push_cast [Nat.cast_sub (show x ≤ e by omega)]; grind
    have h' : (e : Int) ∣ ((1 + R * t : Nat) : Int) := by
      rw [this]; exact Int.dvd_sub (Int.dvd_mul_right _ _) hx
    exact Int.natCast_dvd_natCast.mp h'
  obtain ⟨y, hy⟩ := hdv
  -- `y < e`, so `c = y`.
  have hye : y < e := by
    have : R * t ≤ (e - 1) * (e - 1) := Nat.mul_le_mul (by omega) (by omega)
    have : e * y < e * e := by
      have : (e - 1) * (e - 1) < e * e - 1 := by
        rcases e with _ | e
        · omega
        · simp only [Nat.add_sub_cancel]
          rw [Nat.mul_add, Nat.add_mul]; omega
      omega
    exact Nat.lt_of_mul_lt_mul_left this
  have hc : ((R * t % 2 ^ 64 + 1) % 2 ^ 64 * einv) % 2 ^ 64 = y := by
    rw [Nat.mod_add_mod, show R * t + 1 = 1 + R * t by omega, hy, Nat.mod_mul_mod,
      show e * y * einv = y * (e * einv) by grind, Nat.mul_mod, hinv, Nat.mul_one, Nat.mod_mod,
      Nat.mod_eq_of_lt (by omega)]
  rw [hc]
  -- `e (Q t + y) = L t + 1`.
  have hed : e * (Q * t + y) = L * t + 1 := by
    rw [Nat.mul_add, ← hy, hQR]; grind
  refine inverse_eq (by omega) ?_ ⟨t, ?_⟩
  · -- `Q t + y < L`: `e (Q t + y) = L t + 1 < L e`.
    have : L * t + 1 < L * e := by
      have : L * t + L ≤ L * e := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hte
      omega
    have : e * (Q * t + y) < e * L := by rw [hed, Nat.mul_comm e L]; exact this
    exact Nat.lt_of_mul_lt_mul_left this
  · have : ((e * (Q * t + y) : Nat) : Int) = ((L * t + 1 : Nat) : Int) := by rw [hed]
    push_cast at this
    push_cast at this ⊢
    grind

/-- An odd `e ≥ 3`: no inverse for `L < 2`, or for `gcd(R, e) ≠ 1`. -/
theorem inverse_odd_none {e L Q R : Nat} (he3 : 3 ≤ e) (hQR : L = e * Q + R)
    (h : ¬ (2 ≤ L ∧ Nat.gcd R e = 1)) : Spec.Rsa.inverse e L = none := by
  rcases Nat.lt_or_ge L 2 with hl | hl
  · rcases (show L = 0 ∨ L = 1 by omega) with rfl | rfl
    · rw [inverse_mod_zero, ite_eq_right (show e ≠ 1 by omega)]
    · exact inverse_mod_one e
  · have hg : Nat.gcd R e ≠ 1 := fun hg => h ⟨hl, hg⟩
    refine inverse_none fun h1 => hg ?_
    rw [hQR, Nat.gcd_mul_left_add_right, Nat.gcd_comm] at h1
    exact h1

/-- An even `e`: for an odd `L ≥ 3` with `x (e mod L) ≡ 1` and `x < L`, the
inverse is `x`. -/
theorem inverse_even {e L x : Nat} (hL : 3 ≤ L) (hx : (L : Int) ∣ (x : Int) * ((e % L : Nat) : Int) - 1)
    (hxL : x < L) : Spec.Rsa.inverse e L = some x := by
  refine inverse_eq (by omega) hxL ?_
  obtain ⟨c, hc⟩ := hx
  have h3 : ((e % L : Nat) : Int) + (L : Int) * ((e / L : Nat) : Int) = e := by
    exact_mod_cast Nat.mod_add_div e L
  generalize ((e % L : Nat) : Int) = r at hc h3
  generalize ((e / L : Nat) : Int) = q at h3
  refine ⟨c + x * q, ?_⟩
  rw [← h3]; grind

/-- An even `e`: no inverse unless `L` is odd and at least 3 and
`gcd(e mod L, L) = 1`. -/
theorem inverse_even_none {e L : Nat} (he : e % 2 = 0) (h : ¬ (L % 2 = 1 ∧ 3 ≤ L ∧ Nat.gcd (e % L) L = 1)) :
    Spec.Rsa.inverse e L = none := by
  rcases Nat.lt_or_ge L 2 with hl | hl
  · rcases (show L = 0 ∨ L = 1 by omega) with rfl | rfl
    · rw [inverse_mod_zero, ite_eq_right (show e ≠ 1 by omega)]
    · exact inverse_mod_one e
  · refine inverse_none fun h1 => h ?_
    have hg : Nat.gcd (e % L) L = 1 := by rw [← Nat.gcd_rec, Nat.gcd_comm]; exact h1
    refine ⟨?_, ?_, hg⟩
    · -- An even `L` shares the factor 2 with `e`.
      by_contra hL
      have : 2 ∣ Nat.gcd e L := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero he) (Nat.dvd_of_mod_eq_zero (by omega))
      rw [h1] at this
      omega
    · by_contra hL
      have : L = 2 := by omega
      subst this
      have : 2 ∣ Nat.gcd e 2 := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero he) (Nat.dvd_refl 2)
      rw [h1] at this
      omega

end VG.Proof.RsaKeyGen
