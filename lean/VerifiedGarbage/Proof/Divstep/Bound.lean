import VerifiedGarbage.Proof.Divstep.Hull

/-!
# The divstep bound: runs of the relaxed iteration

A run `(i n, f n, g n)` of rationals takes, at every step, either the even
step `(i + 1, f, g/2)` or the odd one, `(i + 1, f, (g + f)/2)` if `i < 0`
and the swap `(-i, g, (g - f)/2)` else (`Step`). Started at `i = 0` with
`(f, g) / u` in `H1`, its points `(f, g) / (u s^m)` stay in `W (i m)`
(`stable`). With integers `f`, `g`, a nonzero `g m` with `i m = n ≥ 0`
bounds `u s^(m + n)` below by `L = 3047/2048` (`lattice`), and a nonzero `g`
until `m` bounds `u s^m` (`sizeBound`), so `g` reaches zero once
`M s^m ≤ 2753/4096 · L` for `0 ≤ g 0 ≤ f 0 ≤ M` (`endToEnd`).
-/

namespace VG.Proof.Divstep

/-- `field_simp`, then `ring` if it is not done. -/
macro "fsr" : tactic => `(tactic| first | (field_simp; done) | (field_simp; ring))

/-- A step of the relaxed iteration. -/
def Step (i : Int) (f g : ℚ) (i' : Int) (f' g' : ℚ) : Prop :=
  (i' = i + 1 ∧ f' = f ∧ g' = g / 2) ∨
    (if i < 0 then i' = i + 1 ∧ f' = f ∧ g' = (g + f) / 2 else i' = -i ∧ f' = g ∧ g' = (g - f) / 2)

theorem W_pos {n : Nat} {x y : ℚ} : W n x y ↔ Wpos n x y := by
  unfold W; rw [ite_t (by omega)]; rfl

theorem W_neg {j : Nat} (hj : 1 ≤ j) {x y : ℚ} : W (-(j : Int)) x y ↔ Wneg j x y := by
  unfold W; rw [ite_f (by omega), show (-(-(j : Int))).toNat = j by omega]

/-- A step keeps the scaled point in `W`. -/
theorem W_step {i i' : Int} {x y : ℚ} {f g f' g' : ℚ} (c : ℚ) (hc : c ≠ 0) (hx : x = f / c) (hy : y = g / c)
    (h : W i x y) (hs : Step i f g i' f' g') : W i' (f' / (c * s)) (g' / (c * s)) := by
  have hs0 := s_ne
  subst hx hy
  rcases hs with ⟨rfl, hf', hg'⟩ | hs
  · -- The even step.
    rw [hf', hg']
    have e1 : f / (c * s) = f / c / s := by field_simp
    have e2 : g / 2 / (c * s) = g / c / (2 * s) := by fsr
    rw [e1, e2]
    rcases Int.lt_or_le i 0 with hi | hi
    · obtain ⟨j, rfl⟩ : ∃ j : Nat, i = -(j : Int) := ⟨(-i).toNat, by omega⟩
      have hj : 1 ≤ j := by omega
      have := Wneg_even ((W_neg hj).mp h)
      rcases Nat.lt_or_ge j 2 with h2 | h2
      · obtain rfl : j = 1 := by omega
        rw [show -((1 : Nat) : Int) + 1 = ((0 : Nat) : Int) by omega, W_pos]; exact this.1 rfl
      · rw [show -(j : Int) + 1 = -((j - 1 : Nat) : Int) by omega, W_neg (by omega)]; exact this.2 h2
    · obtain ⟨n, rfl⟩ : ∃ n : Nat, i = n := ⟨i.toNat, by omega⟩
      rw [show (n : Int) + 1 = ((n + 1 : Nat) : Int) by omega, W_pos]
      exact Wpos_even (W_pos.mp h)
  · split at hs
    · rename_i hi
      obtain ⟨rfl, hf', hg'⟩ := hs
      rw [hf', hg']
      have e1 : f / (c * s) = f / c / s := by field_simp
      have e2 : (g + f) / 2 / (c * s) = (g / c + f / c) / (2 * s) := by fsr
      rw [e1, e2]
      obtain ⟨j, rfl⟩ : ∃ j : Nat, i = -(j : Int) := ⟨(-i).toNat, by omega⟩
      have hj : 1 ≤ j := by omega
      have := Wneg_odd ((W_neg hj).mp h)
      rcases Nat.lt_or_ge j 2 with h2 | h2
      · obtain rfl : j = 1 := by omega
        rw [show -((1 : Nat) : Int) + 1 = ((0 : Nat) : Int) by omega, W_pos]; exact this.1 rfl
      · rw [show -(j : Int) + 1 = -((j - 1 : Nat) : Int) by omega, W_neg (by omega)]; exact this.2 h2
    · rename_i hi
      obtain ⟨rfl, hf', hg'⟩ := hs
      rw [hf', hg']
      have e1 : g / (c * s) = g / c / s := by field_simp
      have e2 : (g - f) / 2 / (c * s) = (g / c - f / c) / (2 * s) := by fsr
      rw [e1, e2]
      obtain ⟨n, rfl⟩ : ∃ n : Nat, i = n := ⟨i.toNat, by omega⟩
      have := Wpos_odd (W_pos.mp h)
      rcases Nat.lt_or_ge n 1 with h1 | h1
      · obtain rfl : n = 0 := by omega
        rw [show -((0 : Nat) : Int) = ((0 : Nat) : Int) by omega, W_pos]; exact this.1 rfl
      · rw [W_neg h1]; exact this.2 h1

/-- A run of the relaxed iteration from `i = 0`. -/
structure Run (i : Nat → Int) (f g : Nat → ℚ) : Prop where
  i0 : i 0 = 0
  step : ∀ n, Step (i n) (f n) (g n) (i (n + 1)) (f (n + 1)) (g (n + 1))

/-- The points of a run stay in the polygons `W`. -/
theorem stable {i : Nat → Int} {f g : Nat → ℚ} (hr : Run i f g) {u : ℚ} (hu : 0 < u)
    (h0 : H1P (f 0 / u) (g 0 / u)) : ∀ m, W (i m) (f m / (u * s ^ m)) (g m / (u * s ^ m))
  | 0 => by
    rw [hr.i0, show (0 : Int) = ((0 : Nat) : Int) from rfl, W_pos]
    unfold Wpos; rw [ite_t (by omega)]
    simpa using h0
  | m + 1 => by
    have := W_step (u * s ^ m) (by have := s_pos; positivity) rfl rfl (stable hr hu h0 m) (hr.step m)
    rwa [pow_succ, ← mul_assoc]

/-- The lattice scale `L`. -/
abbrev Lsc : ℚ := 3047 / 2048

instance (P : List Row) (x y : ℚ) : Decidable (inP P x y) := by unfold inP; infer_instance

/-- A point `(a, b) / u` of `H1` with `0 < u ≤ L` is `(a, b) / L` scaled. -/
theorem H1_atL {a b u : ℚ} (h : H1P (a / u) (b / u)) (hu : 0 < u) (huL : u ≤ Lsc) : H1P (a / Lsc) (b / Lsc) :=
  inP_congr (H1_shrink h (t := u / Lsc) (by positivity) (by rw [div_le_one (by norm_num)]; exact huL))
    (by field_simp) (by field_simp)

theorem s2_ge : (1 : ℚ) ≤ 2 * s ^ 2 := by unfold s sn sd; norm_num

/-- A nonzero integer `y` with `Wpos n (x / t) (y / t)` bounds `t s^n` below. -/
theorem lattice {n : Nat} {x y : Int} (hy : y ≠ 0) {t : ℚ} (ht : 0 < t) (h : Wpos n (x / t) (y / t)) :
    Lsc < t * s ^ n := by
  have hs := s_pos
  by_contra hc
  have hc := not_lt.mp hc
  have hu : 0 < t * s ^ n := by positivity
  have hy1 : (1 : ℚ) ≤ |(y : ℚ)| := by
    have : (1 : Int) ≤ |y| := Int.one_le_abs hy
    exact_mod_cast this
  unfold Wpos at h
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · rw [ite_t (by omega)] at h
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · rcases Nat.lt_or_ge n 1 with h1 | h1
      · obtain rfl : n = 0 := by omega
        have h' := H1_atL (a := x) (b := y) (u := t) (by simpa using h) ht (by simpa using hc)
        obtain ⟨bx, bY⟩ := H1_box h'
        rw [abs_le] at bx bY
        have hx : x = -1 ∨ x = 0 ∨ x = 1 := by
          have : (-2 : ℚ) < x ∧ (x : ℚ) < 2 := by constructor <;> linarith only [bx.1, bx.2]
          have a : (-2 : Int) < x := by exact_mod_cast this.1
          have b : x < (2 : Int) := by exact_mod_cast this.2
          omega
        have hyv : y = -1 ∨ y = 1 := by
          have : (-2 : ℚ) < y ∧ (y : ℚ) < 2 := by constructor <;> linarith only [bY.1, bY.2]
          have a : (-2 : Int) < y := by exact_mod_cast this.1
          have b : y < (2 : Int) := by exact_mod_cast this.2
          omega
        rcases hx with rfl | rfl | rfl <;> rcases hyv with rfl | rfl <;> revert h' <;> decide +kernel
      · obtain rfl : n = 1 := by omega
        have h' := H1_atL (a := x * s ^ 2) (b := 2 * y * s ^ 2) (u := t * s ^ 1)
          (inP_congr h (by field_simp) (by fsr)) hu hc
        obtain ⟨bx, bY⟩ := H1_box h'
        rw [abs_le] at bx bY
        have hs2 : s ^ 2 = 954973097164321 / 1743039955072900 := by unfold s sn sd; norm_num
        rw [hs2] at bx bY
        have hx : x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 := by
          have : (-3 : ℚ) < x ∧ (x : ℚ) < 3 := by constructor <;> linarith only [bx.1, bx.2]
          have a : (-3 : Int) < x := by exact_mod_cast this.1
          have b : x < (3 : Int) := by exact_mod_cast this.2
          omega
        have hyv : y = -1 ∨ y = 1 := by
          have : (-2 : ℚ) < y ∧ (y : ℚ) < 2 := by constructor <;> linarith only [bY.1, bY.2]
          have a : (-2 : Int) < y := by exact_mod_cast this.1
          have b : y < (2 : Int) := by exact_mod_cast this.2
          omega
        rw [hs2] at h'
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> rcases hyv with rfl | rfl <;> revert h' <;> decide +kernel
    · obtain rfl : n = 2 := by omega
      have h' := H1_atL (a := x * s ^ 4) (b := 4 * y * s ^ 4) (u := t * s ^ 2)
        (inP_congr h (by fsr) (by fsr)) hu hc
      have bY := (H1_box h').2
      have hs4 : (379 / 512 : ℚ) * Lsc / (4 * s ^ 4) < 1 := by unfold s sn sd; norm_num
      have : |(y : ℚ)| * (4 * s ^ 4) / Lsc ≤ 379 / 512 := by
        rw [abs_div, abs_mul, abs_mul, abs_of_pos (show (0 : ℚ) < Lsc by norm_num),
          abs_of_pos (show (0 : ℚ) < 4 by norm_num), abs_of_pos (by positivity : (0 : ℚ) < s ^ 4)] at bY
        linarith only [bY]
      have : |(y : ℚ)| < 1 := by
        rw [div_le_iff₀ (by norm_num)] at this
        rw [div_lt_one (by positivity)] at hs4
        nlinarith only [this, hs4, abs_nonneg (y : ℚ)]
      exact absurd hy1 (not_le.mpr this)
  · rw [ite_f (by omega)] at h
    have h' := H1_atL (a := c32 * x * s ^ (2 * n)) (b := c32 * y * 2 ^ n * s ^ (2 * n)) (u := t * s ^ n)
      (inP_congr h (by rw [pow_mul']; fsr) (by rw [pow_mul', mul_pow]; fsr)) hu hc
    have bY := (H1_box h').2
    have hp : (2 * s ^ 2) ^ 3 ≤ (2 * s ^ 2) ^ n := pow_le_pow_right₀ s2_ge h3
    have hb : (379 / 512 : ℚ) * (33 / 32) * Lsc / (2 * s ^ 2) ^ 3 < 1 := by unfold s sn sd; norm_num
    have e : c32 * y * 2 ^ n * s ^ (2 * n) = c32 * y * (2 * s ^ 2) ^ n := by rw [mul_pow, pow_mul]; ring
    rw [e] at bY
    have hp0 : (0 : ℚ) < (2 * s ^ 2) ^ 3 := by positivity
    have hpn : (0 : ℚ) < (2 * s ^ 2) ^ n := by positivity
    have : |(y : ℚ)| * (2 * s ^ 2) ^ n ≤ (379 / 512) * (33 / 32) * Lsc := by
      rw [abs_div, abs_mul, abs_mul, abs_of_pos (show (0 : ℚ) < Lsc by norm_num),
        abs_of_pos (show (0 : ℚ) < c32 by norm_num), abs_of_pos hpn, div_le_iff₀ (by norm_num)] at bY
      unfold c32 at bY
      linarith only [bY, abs_nonneg (y : ℚ)]
    rw [div_lt_one hp0] at hb
    nlinarith only [this, hb, hp, hy1, hp0, abs_nonneg (y : ℚ)]

/-- `j(i)`: `i` for `i ≥ 0`, `-i - 1` else. -/
def J (i : Int) : Nat := if 0 ≤ i then i.toNat else (-i).toNat - 1

/-- A run whose `g` stays nonzero until `m` has `L < u s^(m + J (i m))`. -/
theorem sizeBound {i : Nat → Int} {f g : Nat → ℚ} (hr : Run i f g) {u : ℚ} (hu : 0 < u)
    (h0 : H1P (f 0 / u) (g 0 / u)) (hf : ∀ n, ∃ z : Int, f n = z) (hg : ∀ n, ∃ z : Int, g n = z) :
    ∀ m, (∀ n ≤ m, g n ≠ 0) → Lsc < u * s ^ (m + J (i m)) := by
  have hs := s_pos
  intro m
  induction m with
  | zero => ?_
  | succ m ih => ?_
  all_goals intro hnz
  · -- `i 0 = 0`.
    obtain ⟨x, hx⟩ := hf 0
    obtain ⟨y, hy⟩ := hg 0
    have h := stable hr hu h0 0
    rw [hr.i0, show (0 : Int) = ((0 : Nat) : Int) from rfl, W_pos] at h
    rw [hx, hy] at h
    have := lattice (n := 0) (x := x) (y := y) (by intro e; exact hnz 0 (Nat.le_refl _) (by rw [hy, e]; simp))
      (t := u * s ^ 0) (by positivity) h
    simpa [hr.i0, J] using this
  · rcases Int.lt_or_le (i (m + 1)) 0 with hi | hi
    · have ih' := ih fun n hn => hnz n (by omega)
      have e : m + J (i m) = m + 1 + J (i (m + 1)) := by
        have st := hr.step m
        unfold J
        rcases st with ⟨h1, -, -⟩ | st
        · rw [ite_f (by omega), ite_f (by omega)]; omega
        · split at st
          · rw [ite_f (by omega), ite_f (by omega)]; omega
          · obtain ⟨h1, -, -⟩ := st
            rw [ite_t (by omega), ite_f (by omega)]; omega
      rw [← e]; exact ih'
    · obtain ⟨x, hx⟩ := hf (m + 1)
      obtain ⟨y, hy⟩ := hg (m + 1)
      have h := stable hr hu h0 (m + 1)
      obtain ⟨n, hn⟩ : ∃ n : Nat, i (m + 1) = n := ⟨(i (m + 1)).toNat, by omega⟩
      rw [hn, W_pos, hx, hy] at h
      have := lattice (x := x) (y := y) (by intro e; exact hnz (m + 1) (Nat.le_refl _) (by rw [hy, e]; simp))
        (by positivity) h
      rw [hn, show J (n : Int) = n by simp [J], pow_add, ← mul_assoc]
      exact this

/-- The fuzziness `2753/4096 · L`. -/
abbrev fuzz : ℚ := 8388391 / 8388608

/-- A run of integers from `0 ≤ g 0 ≤ f 0 ≤ M` reaches `g = 0` by step `m`
when `M s^m ≤ 2753/4096 · L`. -/
theorem endToEnd {i : Nat → Int} {f g : Nat → ℚ} (hr : Run i f g) (hf : ∀ n, ∃ z : Int, f n = z)
    (hg : ∀ n, ∃ z : Int, g n = z) {M : ℚ} (hg0 : 0 ≤ g 0) (hgf : g 0 ≤ f 0) (hfM : f 0 ≤ M) {m : Nat}
    (hm : M * s ^ m ≤ fuzz) : ∃ n ≤ m, g n = 0 := by
  have hs := s_pos
  have hs1 := s_lt_one
  by_contra hc
  have hc : ∀ n ≤ m, g n ≠ 0 := fun n hn e => hc ⟨n, hn, e⟩
  rcases lt_or_eq_of_le (le_trans hg0 (le_trans hgf hfM)) with hM | hM
  · set u := M * (4096 / 2753) with hu
    have hu0 : 0 < u := by positivity
    have q1 : f 0 / M ≤ 1 := (div_le_one hM).mpr hfM
    have q2 : g 0 / M ≤ f 0 / M := div_le_div_of_nonneg_right hgf hM.le
    have q3 : 0 ≤ g 0 / M := div_nonneg hg0 hM.le
    have hin : inP Hinit (f 0 / M) (g 0 / M) := by
      intro r hr
      simp only [Hinit, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> push_cast <;> linarith
    have h0 : H1P (f 0 / u) (g 0 / u) :=
      incl_at inclInit_ok hin (by simp only [inclInit, LinMap.fx, LinMap.q]; push_cast; field_simp; ring)
        (by simp only [inclInit, LinMap.fy, LinMap.q]; push_cast; field_simp; ring)
    have hb := sizeBound hr hu0 h0 hf hg m hc
    have hle : u * s ^ (m + J (i m)) ≤ u * s ^ m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs.le hs1.le (Nat.le_add_right _ _)) hu0.le
    have : u * s ^ m ≤ Lsc := by
      rw [hu, mul_assoc, mul_comm (4096 / 2753 : ℚ), ← mul_assoc]
      have := mul_le_mul_of_nonneg_right hm (show (0 : ℚ) ≤ 4096 / 2753 by norm_num)
      unfold fuzz at this; norm_num at this ⊢; linarith
    linarith
  · exact hc 0 (Nat.zero_le _) (le_antisymm (by rw [hM]; linarith) hg0)

end VG.Proof.Divstep
