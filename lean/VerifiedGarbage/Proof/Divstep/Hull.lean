import VerifiedGarbage.Proof.Divstep.Incl

/-!
# The hulls of the divstep bound: transitions

Bernstein's `hull-light` argument, as J. Harrison checked it in HOL Light
(`Divstep/hull_light.ml`). For `i = δ - 1/2` of the divstep (`i = 0` at the
start), the points `(f, g) / (u s^m)` of a run stay in the polygon
`W i` (`W_even`, `W_odd`): `H1` scaled by powers of `s` and `2` for `i ≥ 0`,
`H0` for `i = -1`, and `H1` of a sheared point for `i ≤ -2`. Each step is
one of the checked inclusions (`Incl`), a scaling of `H1` towards its
origin (`H1_shrink`), a convex combination of two inclusions
(`H1_shear`), or an identity.
-/

namespace VG.Proof.Divstep

/-- `H1` holds `(x, y)`. -/
abbrev H1P (x y : ℚ) : Prop := inP H1 x y
/-- `H0` holds `(x, y)`. -/
abbrev H0P (x y : ℚ) : Prop := inP H0 x y

theorem inP_congr {P : List Row} {x y x' y' : ℚ} (h : inP P x y) (hx : x = x') (hy : y = y') :
    inP P x' y' := hx ▸ hy ▸ h

/-- A polygon is convex. -/
theorem inP_convex {P : List Row} {x₁ y₁ x₂ y₂ t : ℚ} (h₁ : inP P x₁ y₁) (h₂ : inP P x₂ y₂)
    (ht : 0 ≤ t) (ht' : t ≤ 1) : inP P (t * x₁ + (1 - t) * x₂) (t * y₁ + (1 - t) * y₂) := by
  intro r hr
  have a := mul_le_mul_of_nonneg_left (h₁ r hr) ht
  have b := mul_le_mul_of_nonneg_left (h₂ r hr) (by linarith : (0 : ℚ) ≤ 1 - t)
  nlinarith

theorem H1_zero : H1P 0 0 := by
  have : H1.all (fun r => decide (0 ≤ r.2.2)) = true := by decide +kernel
  intro r hr
  have := List.all_eq_true.mp this r hr
  simp only [decide_eq_true_eq] at this
  simp only [mul_zero, add_zero]
  exact_mod_cast this

/-- `H1` scaled towards its origin. -/
theorem H1_shrink {x y t : ℚ} (h : H1P x y) (ht : 0 ≤ t) (ht' : t ≤ 1) : H1P (t * x) (t * y) :=
  inP_congr (inP_convex h H1_zero ht ht') (by ring) (by ring)

/-- `H1` lies in the box `|x| ≤ 8193/8192`, `|y| ≤ 379/512`. -/
theorem H1_box {x y : ℚ} (h : H1P x y) : |x| ≤ 8193 / 8192 ∧ |y| ≤ 379 / 512 := by
  have o := Incl.ok_sound inclOuter_ok (x := x) (y := y) h
  simp only [inclOuter, LinMap.fx, LinMap.fy, LinMap.q, pow_zero, mul_one] at o
  have r1 := o (0, -512, 379) (by simp [Houter])
  have r2 := o (8192, 0, 8193) (by simp [Houter])
  have r3 := o (0, 512, 379) (by simp [Houter])
  have r4 := o (-8192, 0, 8193) (by simp [Houter])
  push_cast at r1 r2 r3 r4
  constructor <;> rw [abs_le] <;> constructor <;> linarith

/-- An inclusion, with its map's coordinates computed. -/
theorem incl_at {I : Incl} (h : I.ok = true) {x y x' y' : ℚ} (hs : inP I.src x y)
    (hx : I.map.fx x y = x') (hy : I.map.fy x y = y') : inP I.dst x' y' :=
  hx ▸ hy ▸ Incl.ok_sound h hs

theorem s_ne : s ≠ 0 := ne_of_gt s_pos

theorem ite_t {α : Sort _} {c : Prop} [Decidable c] (h : c) {x y : α} : (if c then x else y) = x := by
  simp [h]

theorem ite_f {α : Sort _} {c : Prop} [Decidable c] (h : ¬c) {x y : α} : (if c then x else y) = y := by
  simp [h]

/-- The fudge factor `32/33` of the scaled polygons. -/
abbrev c32 : ℚ := 32 / 33

/-- `H1` holds `((X/2 ± Y/16) / s², (Y/2) / s²)` with `(X, Y)`. -/
theorem H1_16 {X Y : ℚ} (h : H1P X Y) :
    H1P ((X / 2 + Y / 16) / s ^ 2) ((Y / 2) / s ^ 2) ∧ H1P ((X / 2 - Y / 16) / s ^ 2) ((Y / 2) / s ^ 2) := by
  have hs := s_ne
  constructor
  · have a := incl_at inclN4scale_ok (x := X) (y := Y) (by exact h) rfl rfl
    refine inP_congr (H1_shrink a (t := c32) (by norm_num) (by norm_num)) ?_ ?_ <;>
      simp only [inclN4scale, LinMap.fx, LinMap.fy, LinMap.q] <;> push_cast <;> field_simp <;> ring
  · have a := incl_at inclN3scale_ok (x := X) (y := Y) (by exact h) rfl rfl
    refine inP_congr (H1_shrink a (t := c32) (by norm_num) (by norm_num)) ?_ ?_ <;>
      simp only [inclN3scale, LinMap.fx, LinMap.fy, LinMap.q] <;> push_cast <;> field_simp <;> ring

/-- `H1` holds `((X/2 ± Y/2^(m+2)) / s², (Y/2) / s²)` with `(X, Y)`, for
`m ≥ 2`: a combination of the two of `H1_16` along the same `y`. -/
theorem H1_shear {X Y : ℚ} (h : H1P X Y) {m : Nat} (hm : 2 ≤ m) :
    H1P ((X / 2 + Y / 2 ^ (m + 2)) / s ^ 2) ((Y / 2) / s ^ 2) ∧
      H1P ((X / 2 - Y / 2 ^ (m + 2)) / s ^ 2) ((Y / 2) / s ^ 2) := by
  obtain ⟨a, b⟩ := H1_16 h
  have hs := s_ne
  have hp : (4 : ℚ) ≤ 2 ^ m := by
    calc (4 : ℚ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hp0 : (0 : ℚ) < 2 ^ m := by positivity
  have e : (2 : ℚ) ^ (m + 2) = 2 ^ m * 4 := by rw [pow_add]; norm_num
  -- `t = (1 + 4/2^m)/2` and `1 - t` of the two points.
  have t0 : (0 : ℚ) ≤ (1 + 4 / 2 ^ m) / 2 := by positivity
  have t1 : (1 + 4 / 2 ^ m) / 2 ≤ (1 : ℚ) := by
    rw [div_le_one (by norm_num)]; have : 4 / 2 ^ m ≤ (1 : ℚ) := by rw [div_le_one hp0]; exact hp
    linarith
  have u0 : (0 : ℚ) ≤ (1 - 4 / 2 ^ m) / 2 := by
    apply div_nonneg _ (by norm_num); have : 4 / 2 ^ m ≤ (1 : ℚ) := by rw [div_le_one hp0]; exact hp
    linarith
  have u1 : (1 - 4 / 2 ^ m) / 2 ≤ (1 : ℚ) := by
    have : (0 : ℚ) ≤ 4 / 2 ^ m := by positivity
    linarith
  constructor
  · refine inP_congr (inP_convex a b t0 t1) ?_ ?_ <;> (try rw [e]) <;> field_simp <;> ring
  · refine inP_congr (inP_convex a b u0 u1) ?_ ?_ <;> (try rw [e]) <;> field_simp <;> ring

/-! ## The polygons `W i` -/

/-- `W i` for `i = n ≥ 0`. -/
def Wpos (n : Nat) (x y : ℚ) : Prop :=
  if n ≤ 2 then H1P (x * s ^ n) (y * (2 * s) ^ n) else H1P (c32 * x * s ^ n) (c32 * y * (2 * s) ^ n)

/-- `W i` for `i = -j ≤ -1`. -/
def Wneg (j : Nat) (x y : ℚ) : Prop :=
  if j = 1 then H0P x y
  else if j = 2 then H1P ((x - 2 * y) * s ^ 3) (4 * x * s ^ 3)
  else H1P (c32 * (x - 2 * y) * s ^ (j + 1)) (c32 * x * s ^ (j + 1) * 2 ^ j)

/-- The polygon of `i = δ - 1/2`. -/
def W (i : Int) (x y : ℚ) : Prop := if 0 ≤ i then Wpos i.toNat x y else Wneg (-i).toNat x y

/-- An even step from `i ≥ 0`. -/
theorem Wpos_even {n : Nat} {x y : ℚ} (h : Wpos n x y) : Wpos (n + 1) (x / s) (y / (2 * s)) := by
  have hs := s_ne
  unfold Wpos at h ⊢
  rcases Nat.lt_or_ge n 2 with hn | hn
  · simp (disch := omega) only [ite_t] at h ⊢
    refine inP_congr h ?_ ?_ <;> rw [pow_succ] <;> field_simp
  · rcases Nat.lt_or_ge n 3 with hn' | hn'
    · obtain rfl : n = 2 := by omega
      simp (disch := omega) only [ite_t] at h; simp (disch := omega) only [ite_f]
      refine inP_congr (H1_shrink h (t := c32) (by norm_num) (by norm_num)) ?_ ?_ <;> first | (field_simp; done) | (field_simp; ring)
    · simp (disch := omega) only [ite_f] at h ⊢
      refine inP_congr h ?_ ?_ <;> rw [pow_succ] <;> field_simp

/-- An odd step from `i ≥ 0`: the swap, to `i = -n`. -/
theorem Wpos_odd {n : Nat} {x y : ℚ} (h : Wpos n x y) :
    (n = 0 → Wpos 0 (y / s) ((y - x) / (2 * s))) ∧ (1 ≤ n → Wneg n (y / s) ((y - x) / (2 * s))) := by
  have hs := s_ne
  unfold Wpos at h
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · subst hn
    simp (disch := omega) only [ite_t, pow_zero, mul_one] at h
    unfold Wpos
    simp (disch := omega) only [ite_t, pow_zero, mul_one]
    refine incl_at incl3_ok (x := x) (y := y) (by exact h) ?_ ?_ <;>
      simp only [incl3, LinMap.fx, LinMap.fy, LinMap.q] <;> push_cast <;> field_simp <;> ring
  · unfold Wneg
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 1 := by omega
      simp (disch := omega) only [ite_t, pow_one] at h ⊢
      refine incl_at incl5_ok (x := x * s) (y := y * (2 * s)) (by exact h) ?_ ?_ <;>
        simp only [incl5, LinMap.fx, LinMap.fy, LinMap.q] <;> push_cast <;> field_simp <;> ring
    · rcases Nat.lt_or_ge n 3 with h3 | h3
      · obtain rfl : n = 2 := by omega
        simp (disch := omega) only [ite_t] at h
        simp (disch := omega) only [ite_f]
        refine inP_congr h ?_ ?_ <;> field_simp <;> ring
      · simp (disch := omega) only [ite_f] at h ⊢
        refine inP_congr h ?_ ?_ <;> simp only [pow_succ, mul_pow] <;> first | (field_simp; done) | (field_simp; ring)

/-- A step from `i = -j` to `i + 1` with `g` even. -/
theorem Wneg_even {j : Nat} {x y : ℚ} (h : Wneg j x y) :
    (j = 1 → Wpos 0 (x / s) (y / (2 * s))) ∧ (2 ≤ j → Wneg (j - 1) (x / s) (y / (2 * s))) := by
  have hs := s_ne
  unfold Wneg at h
  refine ⟨fun hj => ?_, fun hj => ?_⟩
  · subst hj
    simp only [↓reduceIte] at h
    unfold Wpos; simp (disch := omega) only [ite_t, pow_zero, mul_one]
    refine incl_at incl0_ok (x := x) (y := y) (by exact h) ?_ ?_ <;>
      simp only [incl0, LinMap.fx, LinMap.fy, LinMap.q] <;> push_cast <;> field_simp <;> ring
  · unfold Wneg
    rcases Nat.lt_or_ge j 3 with h3 | h3
    · obtain rfl : j = 2 := by omega
      simp (disch := omega) only [ite_f] at h ⊢
      refine incl_at inclN2_ok (x := (x - 2 * y) * s ^ 3) (y := 4 * x * s ^ 3) (by exact h) ?_ ?_ <;>
        simp only [inclN2, LinMap.fx, LinMap.fy, LinMap.q] <;> push_cast <;> field_simp <;> ring
    · simp (disch := omega) only [ite_f] at h
      rcases Nat.lt_or_ge j 4 with h4 | h4
      · obtain rfl : j = 3 := by omega
        simp (disch := omega) only [ite_f]
        refine incl_at inclN4scale_ok (x := c32 * (x - 2 * y) * s ^ (3 + 1))
          (y := c32 * x * s ^ (3 + 1) * 2 ^ 3) (by exact h) ?_ ?_ <;>
          simp only [inclN4scale, LinMap.fx, LinMap.fy, LinMap.q] <;> push_cast <;> field_simp <;> ring
      · simp (disch := omega) only [ite_f]
        obtain ⟨k, rfl⟩ : ∃ k, j = k + 4 := ⟨j - 4, by omega⟩
        refine inP_congr (H1_shear h (m := k + 3) (by omega)).1 ?_ ?_ <;>
          (simp only [show k + 4 - 1 = k + 3 from by omega, pow_succ]
           first | (field_simp; done) | (field_simp; ring))

/-- A step from `i = -j` to `i + 1` with `g` odd. -/
theorem Wneg_odd {j : Nat} {x y : ℚ} (h : Wneg j x y) :
    (j = 1 → Wpos 0 (x / s) ((y + x) / (2 * s))) ∧ (2 ≤ j → Wneg (j - 1) (x / s) ((y + x) / (2 * s))) := by
  have hs := s_ne
  unfold Wneg at h
  refine ⟨fun hj => ?_, fun hj => ?_⟩
  · subst hj
    simp only [↓reduceIte] at h
    unfold Wpos; simp (disch := omega) only [ite_t, pow_zero, mul_one]
    refine incl_at incl1_ok (x := x) (y := y) (by exact h) ?_ ?_ <;>
      simp only [incl1, LinMap.fx, LinMap.fy, LinMap.q] <;> push_cast <;> field_simp <;> ring
  · unfold Wneg
    rcases Nat.lt_or_ge j 3 with h3 | h3
    · obtain rfl : j = 2 := by omega
      simp (disch := omega) only [ite_f] at h ⊢
      refine incl_at inclN1_ok (x := (x - 2 * y) * s ^ 3) (y := 4 * x * s ^ 3) (by exact h) ?_ ?_ <;>
        simp only [inclN1, LinMap.fx, LinMap.fy, LinMap.q] <;> push_cast <;> field_simp <;> ring
    · simp (disch := omega) only [ite_f] at h
      rcases Nat.lt_or_ge j 4 with h4 | h4
      · obtain rfl : j = 3 := by omega
        simp (disch := omega) only [ite_f]
        refine incl_at inclN3scale_ok (x := c32 * (x - 2 * y) * s ^ (3 + 1))
          (y := c32 * x * s ^ (3 + 1) * 2 ^ 3) (by exact h) ?_ ?_ <;>
          simp only [inclN3scale, LinMap.fx, LinMap.fy, LinMap.q] <;> push_cast <;> field_simp <;> ring
      · simp (disch := omega) only [ite_f]
        obtain ⟨k, rfl⟩ : ∃ k, j = k + 4 := ⟨j - 4, by omega⟩
        refine inP_congr (H1_shear h (m := k + 3) (by omega)).2 ?_ ?_ <;>
          (simp only [show k + 4 - 1 = k + 3 from by omega, pow_succ]
           first | (field_simp; done) | (field_simp; ring))

end VG.Proof.Divstep
