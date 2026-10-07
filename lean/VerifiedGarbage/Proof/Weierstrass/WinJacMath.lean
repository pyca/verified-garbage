import VerifiedGarbage.Proof.Weierstrass.Window5
import VerifiedGarbage.Proof.Weierstrass.Booth
import VerifiedGarbage.Proof.Weierstrass.PrimeOrder

/-!
# Windows of 5 bits in Jacobian coordinates: why no addition is exceptional

The Jacobian window method (`Impl/Weierstrass/X86_64/WinJac.lean`) adds with
formulas that are wrong for equal or opposite points. For a curve of prime
order `n` (`PrimeOrder`), integer multiples of a point `P ≠ O` agree only for
integers congruent modulo `n` (`zmul_dvd`).

With `k' = k + 16 Σ_{j<J} 32^j`, the accumulator before digit `j` is
`[32 e]P` for `e = winE k' J (j + 1)`, which is `⌊(k + 16 Σ_{i<j+1} 32^i) / 32^(j+1)⌋`
(`winE_closed`): below `n` for `k < n`, and for `j ≥ 1` below `n - 32`
(`winE_lt`). Adding the digit's point `[d]P` (`winPt`) to `[32 e]P` for
`e ≥ 1` and `d ≠ 0` is never exceptional (`loop_noexc`): `32 e ≡ d` would
need `0 < 32 e - d < n`, and `32 e ≡ -d` would need `winE k' J j = n - 2|d|`,
which only `j = 0`, `k = n - 2 |d|` allows, and then the digit `d_0` is
`((n + 16) mod 32) - 16 - 2 |d| ≠ -|d|` for `n ≡ 17 (mod 32)`, as P-256's.
The table's mixed additions `[m]P + P`, `2 ≤ m ≤ 15`, are not either
(`tbl_noexc`).
-/

namespace VG.Proof.Weierstrass.Window5

open Spec.Weierstrass

variable {C : Curve}

/-! ## Multiples of a point of prime order -/

theorem mul_zero_pt (P : Point C) : mul 0 P = .infinity := by
  rw [Spec.Weierstrass.mul]; simp

/-- In a group of prime order, `[a]P = [b]P` for `P ≠ O` only if `a ≡ b (mod n)`. -/
theorem zmul_dvd (hC : Law C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) {a b : Int} (h : zmul a P = zmul b P) : (C.n : Int) ∣ a - b := by
  obtain ⟨A, _, f, hf⟩ := hC.group
  have hinf : f .infinity = 0 := by
    have := hf.mul hP 0
    rw [mul_zero_pt, Int.natCast_zero, Lean.Grind.IntModule.zero_zsmul] at this
    exact this
  have hab : (a - b) • f P = 0 := by
    have h' := congrArg f h
    rw [hC.group_zmul hf hP, hC.group_zmul hf hP] at h'
    rw [Int.sub_eq_add_neg, Lean.Grind.IntModule.add_zsmul, Lean.Grind.IntModule.neg_zsmul, h']
    grind
  have key : ∀ m : Nat, (m : Int) • f P = 0 → C.n ∣ m := fun m hm =>
    hO P hP hP0 m (hf.inj (hC.onCurve_mul hP m) rfl (by rw [hf.mul hP, hm, hinf]))
  rcases Int.natAbs_eq (a - b) with e | e
  · have := key (a - b).natAbs (by rw [← e]; exact hab)
    rw [e]; exact Int.natCast_dvd_natCast.mpr this
  · have hm : ((a - b).natAbs : Int) • f P = 0 := by
      rw [show ((a - b).natAbs : Int) = -(a - b) by omega, Lean.Grind.IntModule.neg_zsmul, hab]; grind
    have := key _ hm
    rw [e]; exact Int.dvd_neg.mpr (Int.natCast_dvd_natCast.mpr this)

/-- `[m]P ≠ O` for `0 < m < n` and `P ≠ O`. -/
theorem mul_ne_infinity (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) {m : Nat} (h1 : 1 ≤ m) (hm : m < C.n) : mul m P ≠ .infinity := fun h =>
  absurd (Nat.le_of_dvd (by omega) (hO P hP hP0 m h)) (by omega)

/-- An integer of `(0, n)` is no multiple of `n`. -/
theorem not_dvd_of_pos_lt {n : Nat} {x : Int} (h0 : 0 < x) (hx : x < n) : ¬ (n : Int) ∣ x := by
  intro ⟨c, hc⟩
  rcases Int.lt_or_le c 1 with h | h
  · have : c ≤ 0 := by omega
    have : (n : Int) * c ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) this
    omega
  · have : (n : Int) * 1 ≤ n * c := Int.mul_le_mul_of_nonneg_left h (by omega)
    omega

/-! ## The accumulator's multiples -/

/-- The accumulator's multiple before digit `j - 1`: `⌊(k + 16 Σ_{i<j} 32^i) / 32^j⌋`. -/
theorem winE_closed (k : Nat) {J j : Nat} (hj : j ≤ J) :
    winE (k + 16 * geom J) J j = (k + 16 * geom j) / 32 ^ j := by
  have hpos : 0 < 32 ^ j := Nat.pow_pos (by decide)
  have e : 16 * geom J = 16 * geom j + 32 ^ j * (16 * geom (J - j)) := by
    have := geom_add j (J - j)
    rw [Nat.add_sub_cancel' hj] at this
    rw [this, Nat.mul_add, Nat.mul_left_comm]
  unfold winE
  rw [e, ← Nat.add_assoc, Nat.add_mul_div_left _ _ hpos, Nat.add_sub_cancel]

theorem winE_zero' (k J : Nat) : winE (k + 16 * geom J) J 0 = k := by
  rw [winE_closed k (Nat.zero_le _)]; simp [geom]

theorem winE_le (k : Nat) {J j : Nat} (hj : j ≤ J) : winE (k + 16 * geom J) J j ≤ k := by
  rw [winE_closed k hj]
  rcases Nat.eq_zero_or_pos j with rfl | h1
  · simp [geom]
  · have hg := half_geom_lt j
    have hD : 32 ≤ 32 ^ j := by
      calc 32 = 32 ^ 1 := rfl
        _ ≤ 32 ^ j := Nat.pow_le_pow_right (by decide) h1
    have hpos : 0 < 32 ^ j := by omega
    have h₁ : (k + 16 * geom j) / 32 ^ j ≤ (k + 32 ^ j) / 32 ^ j := Nat.div_le_div_right (by omega)
    rw [Nat.add_div_right _ hpos] at h₁
    have h₂ : k / 32 ^ j ≤ k / 32 := Nat.div_le_div_left hD (by decide)
    have h₃ : k / 32 * 32 ≤ k := Nat.div_mul_le_self k 32
    by_cases hk : k < 32
    · have : k / 32 = 0 := Nat.div_eq_of_lt hk
      have : (k + 16 * geom j) / 32 ^ j ≤ 1 := by omega
      -- `k + 16 Σ < 32^j` gives `0`, else `k ≥ 16`.
      by_cases hk' : k + 16 * geom j < 32 ^ j
      · rw [Nat.div_eq_of_lt hk']; exact Nat.zero_le _
      · have hg1 : geom j = 1 + 32 * geom (j - 1) := by
          rw [show j = j - 1 + 1 by omega, geom_succ_left, Nat.add_sub_cancel]
        have h32 : 32 ^ j = 32 * 32 ^ (j - 1) := by
          rw [← Nat.pow_succ']; congr 1; omega
        have := half_geom_lt (j - 1)
        omega
    · omega

/-- For `j ≥ 1`, the accumulator's multiple is far below `n`. -/
theorem winE_lt_sub {n k J j : Nat} (hn : 64 ≤ n) (hk : k < n) (hj : j ≤ J) (h1 : 1 ≤ j) :
    winE (k + 16 * geom J) J j + 33 ≤ n := by
  rw [winE_closed k hj]
  have hg := half_geom_lt j
  have hD : 32 ≤ 32 ^ j := by
    calc 32 = 32 ^ 1 := rfl
      _ ≤ 32 ^ j := Nat.pow_le_pow_right (by decide) h1
  have hpos : 0 < 32 ^ j := by omega
  have h₁ : (k + 16 * geom j) / 32 ^ j ≤ (k + 32 ^ j) / 32 ^ j := Nat.div_le_div_right (by omega)
  rw [Nat.add_div_right _ hpos] at h₁
  have h₂ : k / 32 ^ j ≤ k / 32 := Nat.div_le_div_left hD (by decide)
  have h₃ : k / 32 * 32 ≤ k := Nat.div_mul_le_self k 32
  omega

/-- The digit of window `0`: `(k + 16) mod 32`. -/
theorem nib_zero (k : Nat) {J : Nat} (hJ : 1 ≤ J) : nib (k + 16 * geom J) 0 = (k + 16) % 32 := by
  have hg : geom J = 1 + 32 * geom (J - 1) := by
    rw [show J = J - 1 + 1 by omega, geom_succ_left, Nat.add_sub_cancel]
  unfold nib
  rw [Nat.pow_zero, Nat.div_one, hg]
  omega

theorem nib_lt (k j : Nat) : nib k j < 32 := Nat.mod_lt _ (by decide)

/-- The point of digit `j` as an integer multiple. -/
theorem winPt_zmul (P : Point C) (k j : Nat) :
    winPt C P k j = zmul ((nib k j : Int) - 16) P := by
  unfold winPt zmul
  by_cases h : 16 ≤ nib k j
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true (by omega))]; congr 1; omega
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    congr 2; omega

/-! ## No exceptional addition -/

/-- The loop's addition of digit `j`'s point to `[32 e]P`, `e ≥ 1`: the
points differ and are not opposite. -/
theorem loop_noexc (hC : Law C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) (hn17 : C.n % 32 = 17) (hn64 : 64 ≤ C.n) {k J j : Nat} (hk : k < C.n)
    (hj : j < J) (he : 1 ≤ winE (k + 16 * geom J) J (j + 1)) :
    mul (32 * winE (k + 16 * geom J) J (j + 1)) P ≠ winPt C P (k + 16 * geom J) j ∧
      Spec.Weierstrass.add (mul (32 * winE (k + 16 * geom J) J (j + 1)) P)
        (winPt C P (k + 16 * geom J) j) ≠ .infinity := by
  have hs := winE_step (k := k + 16 * geom J) (J := J) (j := j) (Nat.le_add_left _ _) hj
  have hwl := winE_le k (J := J) (j := j) (by omega)
  have hv := nib_lt (k + 16 * geom J) j
  generalize hee : winE (k + 16 * geom J) J (j + 1) = e at he hs ⊢
  generalize hw : winE (k + 16 * geom J) J j = w at hs hwl
  generalize hvv : nib (k + 16 * geom J) j = v at hs hv
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [winPt_zmul, hvv, ← zmul_natCast] at h
    have hdv := zmul_dvd hC hO hP hP0 h
    rcases Nat.lt_or_ge v 16 with hv16 | hv16
    · -- `32 e + (16 - v) = w + 2 (16 - v)` is `n`.
      obtain ⟨c, hc⟩ := hdv
      have hc1 : c = 1 := by
        rcases Int.lt_or_le c 1 with h1 | h1
        · have : (C.n : Int) * c ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega)
          omega
        · rcases Int.lt_or_le c 2 with h2 | h2
          · omega
          · have : (C.n : Int) * 2 ≤ C.n * c := Int.mul_le_mul_of_nonneg_left h2 (by omega)
            omega
      subst hc1
      rcases Nat.eq_zero_or_pos j with rfl | hj1
      · rw [winE_zero'] at hw
        rw [nib_zero k (by omega)] at hvv
        omega
      · have := winE_lt_sub hn64 hk (J := J) (j := j) (by omega) hj1
        omega
    · exact not_dvd_of_pos_lt (n := C.n) (x := ((32 * e : Nat) : Int) - ((v : Int) - 16)) (by omega)
        (by omega) hdv
  · rw [← hee, win_add hC hP (Nat.le_add_left _ _) hj, hw] at h
    exact mul_ne_infinity hO hP hP0 (m := w) (by omega) (by omega) h

/-- The table's mixed addition `[m]P + P`, `2 ≤ m ≤ 15`, for `n > 16`. -/
theorem tbl_noexc (hC : Law C) (hO : PrimeOrder C) {P : Point C} (hP : onCurve C P = true)
    (hP0 : P ≠ .infinity) (hn : 17 ≤ C.n) {m : Nat} (h2 : 2 ≤ m) (h15 : m ≤ 15) :
    mul m P ≠ P ∧ Spec.Weierstrass.add (mul m P) P ≠ .infinity := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : zmul (m : Int) P = zmul (1 : Nat) P := by
      rw [zmul_natCast, zmul_natCast, mul_one_pt, h]
    exact not_dvd_of_pos_lt (n := C.n) (x := (m : Int) - (1 : Nat)) (by omega) (by omega)
      (zmul_dvd hC hO hP hP0 h')
  · rw [show Spec.Weierstrass.add (mul m P) P = Spec.Weierstrass.add (mul m P) (mul 1 P) by
      rw [mul_one_pt], hC.add_mul_mul hP] at h
    exact mul_ne_infinity hO hP hP0 (m := m + 1) (by omega) (by omega) h

/-- `[a]([b]P) = [a b]P`. -/
theorem mul_mul (hC : Law C) {P : Point C} (hP : onCurve C P = true) (a b : Nat) :
    mul a (mul b P) = mul (a * b) P := by
  induction a with
  | zero => rw [mul_zero_pt, Nat.zero_mul, mul_zero_pt]
  | succ a ih =>
    rw [← hC.add_mul_mul (hC.onCurve_mul hP b) a 1, mul_one_pt, ih, hC.add_mul_mul hP, Nat.succ_mul]

end VG.Proof.Weierstrass.Window5
