import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Framework.PowLit

/-!
# Polygons and their images: a checker

A polygon is a list of rows `(a, b, c)`, the half-planes `a x + b y ≤ c`
(`inP`). A linear map `(x, y) ↦ (a00 x + a01 y, a10 x + a11 y) / (2^e s^k)`,
for the constant `s = 30902639/41749730` of the divstep bound, sends a
polygon into another if every row of the target is a nonnegative
combination of two rows of the source (Farkas), which `inclOk` checks in
integers, given the two rows for each target row (`Incl.ok_sound`).
-/

namespace VG.Proof.Divstep

/-- A row `(a, b, c)`: the half-plane `a x + b y ≤ c`. -/
abbrev Row := Int × Int × Int

/-- `(x, y)` is in every half-plane of `P`. -/
def inP (P : List Row) (x y : ℚ) : Prop := ∀ r ∈ P, (r.1 : ℚ) * x + r.2.1 * y ≤ r.2.2

/-- The contraction of the bound, `s`, as numerator over denominator. -/
def sn : Nat := 30902639
def sd : Nat := 41749730
def s : ℚ := sn / sd

theorem s_pos : 0 < s := by unfold s sn sd; norm_num
theorem s_lt_one : s < 1 := by unfold s sn sd; norm_num

/-- `(x, y) ↦ (a00 x + a01 y, a10 x + a11 y) / (2^e s^k)`. -/
structure LinMap where
  a00 : Int
  a01 : Int
  a10 : Int
  a11 : Int
  e : Nat
  k : Nat

/-- The scale `2^e s^k`. -/
def LinMap.q (L : LinMap) : ℚ := 2 ^ L.e * s ^ L.k

def LinMap.fx (L : LinMap) (x y : ℚ) : ℚ := (L.a00 * x + L.a01 * y) / L.q
def LinMap.fy (L : LinMap) (x y : ℚ) : ℚ := (L.a10 * x + L.a11 * y) / L.q

theorem LinMap.q_pos (L : LinMap) : 0 < L.q := by
  unfold LinMap.q; have := s_pos; positivity

/-- Row `d` of the target bounded by the combination of the source's `r1` and
`r2` (with their determinant's sign: the multipliers are nonnegative and the
combined bound is within `d`'s). -/
def rowOk (L : LinMap) (r1 r2 d : Row) : Bool :=
  let G := d.1 * L.a00 + d.2.1 * L.a10
  let H := d.1 * L.a01 + d.2.1 * L.a11
  let D := r1.1 * r2.2.1 - r2.1 * r1.2.1
  let Mn := G * r2.2.1 - H * r2.1
  let Nn := r1.1 * H - r1.2.1 * G
  let lhs := (Mn * r1.2.2 + Nn * r2.2.2) * (sd : Int) ^ L.k
  let rhs := d.2.2 * 2 ^ L.e * (sn : Int) ^ L.k * D
  if 0 < D then decide (0 ≤ Mn) && decide (0 ≤ Nn) && decide (lhs ≤ rhs)
  else decide (D < 0) && decide (Mn ≤ 0) && decide (Nn ≤ 0) && decide (rhs ≤ lhs)

/-- Every row of the target checked against the source's rows its certificate
names (the row `(0, 0, 0)`, `0 ≤ 0`, past the source's end). -/
def inclOk (L : LinMap) (src : List Row) : List Row → List (Nat × Nat) → Bool
  | [], [] => true
  | d :: ds, (i, j) :: cs =>
    rowOk L (src.getD i (0, 0, 0)) (src.getD j (0, 0, 0)) d && inclOk L src ds cs
  | _, _ => false

/-- An inclusion: a map, its source and target, and a certificate. -/
structure Incl where
  map : LinMap
  src : List Row
  dst : List Row
  cert : List (Nat × Nat)

def Incl.ok (I : Incl) : Bool := inclOk I.map I.src I.dst I.cert

theorem s_pow (k : Nat) : s ^ k = (sn : ℚ) ^ k / (sd : ℚ) ^ k := by unfold s; rw [div_pow]

theorem sd_pow_pos (k : Nat) : (0 : ℚ) < (sd : ℚ) ^ k := by unfold sd; positivity

theorem rowOk_sound {L : LinMap} {r1 r2 d : Row} (h : rowOk L r1 r2 d = true) {x y : ℚ}
    (h1 : (r1.1 : ℚ) * x + r1.2.1 * y ≤ r1.2.2) (h2 : (r2.1 : ℚ) * x + r2.2.1 * y ≤ r2.2.2) :
    (d.1 : ℚ) * L.fx x y + d.2.1 * L.fy x y ≤ d.2.2 := by
  obtain ⟨a1, b1, c1⟩ := r1
  obtain ⟨a2, b2, c2⟩ := r2
  obtain ⟨g, hh, c⟩ := d
  simp only at h1 h2 ⊢
  have hq := L.q_pos
  have hsd := sd_pow_pos L.k
  -- The target row in terms of `G x + H y`.
  have key : (g : ℚ) * L.fx x y + hh * L.fy x y =
      (((g * L.a00 + hh * L.a10 : Int) : ℚ) * x + ((g * L.a01 + hh * L.a11 : Int) : ℚ) * y) / L.q := by
    unfold LinMap.fx LinMap.fy; push_cast; field_simp; ring
  rw [key, div_le_iff₀ hq]
  simp only [rowOk] at h
  generalize g * L.a00 + hh * L.a10 = G at h ⊢
  generalize g * L.a01 + hh * L.a11 = H at h ⊢
  generalize hD : a1 * b2 - a2 * b1 = D at h
  generalize hM : G * b2 - H * a2 = Mn at h
  generalize hN : a1 * H - b1 * G = Nn at h
  -- The Farkas combination: `D (G x + H y) = Mn (a1 x + b1 y) + Nn (a2 x + b2 y)`.
  have comb : (D : ℚ) * ((G : ℚ) * x + H * y) = (Mn : ℚ) * (a1 * x + b1 * y) + (Nn : ℚ) * (a2 * x + b2 * y) := by
    have iA : Mn * a1 + Nn * a2 = G * D := by rw [← hM, ← hN, ← hD]; ring
    have iB : Mn * b1 + Nn * b2 = H * D := by rw [← hM, ← hN, ← hD]; ring
    have eA := congrArg (fun z : Int => (z : ℚ)) iA
    have eB := congrArg (fun z : Int => (z : ℚ)) iB
    push_cast at eA eB
    linear_combination (-x) * eA + (-y) * eB
  -- The combined bound, `(Mn c1 + Nn c2) / D ≤ c q`, scaled.
  have eq : (c : ℚ) * L.q * D = ((c : ℚ) * 2 ^ L.e * (sn : ℚ) ^ L.k * D) / (sd : ℚ) ^ L.k := by
    unfold LinMap.q; rw [s_pow]; field_simp
  split at h
  · rename_i hDp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hMp, hNp⟩, hl⟩ := h
    have hDq : (0 : ℚ) < D := by exact_mod_cast hDp
    have hMq : (0 : ℚ) ≤ Mn := by exact_mod_cast hMp
    have hNq : (0 : ℚ) ≤ Nn := by exact_mod_cast hNp
    have hlq : ((Mn : ℚ) * c1 + Nn * c2) * (sd : ℚ) ^ L.k ≤ (c : ℚ) * 2 ^ L.e * (sn : ℚ) ^ L.k * D := by
      exact_mod_cast hl
    have s1 := mul_le_mul_of_nonneg_left h1 hMq
    have s2 := mul_le_mul_of_nonneg_left h2 hNq
    have h3 : (Mn : ℚ) * c1 + Nn * c2 ≤ c * L.q * D := by rw [eq, le_div_iff₀ hsd]; exact hlq
    have hle : (D : ℚ) * ((G : ℚ) * x + H * y) ≤ D * (c * L.q) := by
      rw [comb]; linarith
    exact le_of_mul_le_mul_left hle hDq
  · rename_i hDp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hDn, hMp⟩, hNp⟩, hl⟩ := h
    have hDq : (D : ℚ) < 0 := by exact_mod_cast hDn
    have hMq : (Mn : ℚ) ≤ 0 := by exact_mod_cast hMp
    have hNq : (Nn : ℚ) ≤ 0 := by exact_mod_cast hNp
    have hlq : (c : ℚ) * 2 ^ L.e * (sn : ℚ) ^ L.k * D ≤ ((Mn : ℚ) * c1 + Nn * c2) * (sd : ℚ) ^ L.k := by
      exact_mod_cast hl
    have s1 := mul_le_mul_of_nonpos_left h1 hMq
    have s2 := mul_le_mul_of_nonpos_left h2 hNq
    have h3 : c * L.q * D ≤ (Mn : ℚ) * c1 + Nn * c2 := by rw [eq, div_le_iff₀ hsd]; exact hlq
    have hle : (-D : ℚ) * ((G : ℚ) * x + H * y) ≤ (-D) * (c * L.q) := by
      have := comb; nlinarith
    exact le_of_mul_le_mul_left hle (by linarith)

theorem getD_row {P : List Row} {x y : ℚ} (h : inP P x y) (i : Nat) :
    ((P.getD i (0, 0, 0)).1 : ℚ) * x + (P.getD i (0, 0, 0)).2.1 * y ≤ (P.getD i (0, 0, 0)).2.2 := by
  rw [List.getD_eq_getElem?_getD]
  cases hP : P[i]? with
  | none => simp
  | some r => exact h r (List.mem_of_getElem? hP)

theorem inclOk_sound {L : LinMap} {src : List Row} :
    ∀ (dst : List Row) (cert : List (Nat × Nat)), inclOk L src dst cert = true →
      ∀ x y, inP src x y → inP dst (L.fx x y) (L.fy x y)
  | [], [], _, _, _, _ => fun _ h => absurd h List.not_mem_nil
  | d :: ds, (i, j) :: cs, h, x, y, hs => by
    simp only [inclOk, Bool.and_eq_true] at h
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact rowOk_sound h.1 (getD_row hs i) (getD_row hs j)
    · exact inclOk_sound ds cs h.2 x y hs r hr
  | [], _ :: _, h, _, _, _ => by simp [inclOk] at h
  | _ :: _, [], h, _, _, _ => by simp [inclOk] at h

/-- A checked inclusion: its map sends its source into its target. -/
theorem Incl.ok_sound {I : Incl} (h : I.ok = true) {x y : ℚ} (hs : inP I.src x y) :
    inP I.dst (I.map.fx x y) (I.map.fy x y) :=
  inclOk_sound I.dst I.cert h x y hs

end VG.Proof.Divstep
