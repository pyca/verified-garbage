import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import VerifiedGarbage.Proof.Framework.PowLit
import Mathlib.Data.Int.ModEq
import Mathlib.Data.BitVec

/- Proofs formerly in `VerifiedGarbage.Proof.Divstep.Check`. -/
section

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
def inP (P : List VG.Proof.Divstep.Row) (x y : ℚ) : Prop := ∀ r ∈ P, (r.1 : ℚ) * x + r.2.1 * y ≤ r.2.2

/-- The contraction of the bound, `s`, as numerator over denominator. -/
def sn : Nat := 30902639
def sd : Nat := 41749730
def s : ℚ := VG.Proof.Divstep.sn / VG.Proof.Divstep.sd

theorem s_pos : 0 < VG.Proof.Divstep.s := by unfold VG.Proof.Divstep.s VG.Proof.Divstep.sn VG.Proof.Divstep.sd; norm_num
theorem s_lt_one : VG.Proof.Divstep.s < 1 := by unfold VG.Proof.Divstep.s VG.Proof.Divstep.sn VG.Proof.Divstep.sd; norm_num

/-- `(x, y) ↦ (a00 x + a01 y, a10 x + a11 y) / (2^e s^k)`. -/
structure LinMap where
  a00 : Int
  a01 : Int
  a10 : Int
  a11 : Int
  e : Nat
  k : Nat

/-- The scale `2^e s^k`. -/
def LinMap.q (L : VG.Proof.Divstep.LinMap) : ℚ := 2 ^ L.e * VG.Proof.Divstep.s ^ L.k

def LinMap.fx (L : VG.Proof.Divstep.LinMap) (x y : ℚ) : ℚ := (L.a00 * x + L.a01 * y) / L.q
def LinMap.fy (L : VG.Proof.Divstep.LinMap) (x y : ℚ) : ℚ := (L.a10 * x + L.a11 * y) / L.q

theorem LinMap.q_pos (L : VG.Proof.Divstep.LinMap) : 0 < L.q := by
  unfold LinMap.q; have := VG.Proof.Divstep.s_pos; positivity

/-- Row `d` of the target bounded by the combination of the source's `r1` and
`r2` (with their determinant's sign: the multipliers are nonnegative and the
combined bound is within `d`'s). -/
def rowOk (L : VG.Proof.Divstep.LinMap) (r1 r2 d : VG.Proof.Divstep.Row) : Bool :=
  let G := d.1 * L.a00 + d.2.1 * L.a10
  let H := d.1 * L.a01 + d.2.1 * L.a11
  let D := r1.1 * r2.2.1 - r2.1 * r1.2.1
  let Mn := G * r2.2.1 - H * r2.1
  let Nn := r1.1 * H - r1.2.1 * G
  let lhs := (Mn * r1.2.2 + Nn * r2.2.2) * (VG.Proof.Divstep.sd : Int) ^ L.k
  let rhs := d.2.2 * 2 ^ L.e * (VG.Proof.Divstep.sn : Int) ^ L.k * D
  if 0 < D then decide (0 ≤ Mn) && decide (0 ≤ Nn) && decide (lhs ≤ rhs)
  else decide (D < 0) && decide (Mn ≤ 0) && decide (Nn ≤ 0) && decide (rhs ≤ lhs)

/-- Every row of the target checked against the source's rows its certificate
names (the row `(0, 0, 0)`, `0 ≤ 0`, past the source's end). -/
def inclOk (L : VG.Proof.Divstep.LinMap) (src : List VG.Proof.Divstep.Row) : List VG.Proof.Divstep.Row → List (Nat × Nat) → Bool
  | [], [] => true
  | d :: ds, (i, j) :: cs =>
    VG.Proof.Divstep.rowOk L (src.getD i (0, 0, 0)) (src.getD j (0, 0, 0)) d && VG.Proof.Divstep.inclOk L src ds cs
  | _, _ => false

/-- An inclusion: a map, its source and target, and a certificate. -/
structure Incl where
  map : VG.Proof.Divstep.LinMap
  src : List VG.Proof.Divstep.Row
  dst : List VG.Proof.Divstep.Row
  cert : List (Nat × Nat)

def Incl.ok (I : VG.Proof.Divstep.Incl) : Bool := VG.Proof.Divstep.inclOk I.map I.src I.dst I.cert

theorem s_pow (k : Nat) : VG.Proof.Divstep.s ^ k = (VG.Proof.Divstep.sn : ℚ) ^ k / (VG.Proof.Divstep.sd : ℚ) ^ k := by unfold VG.Proof.Divstep.s; rw [div_pow]

theorem sd_pow_pos (k : Nat) : (0 : ℚ) < (VG.Proof.Divstep.sd : ℚ) ^ k := by unfold VG.Proof.Divstep.sd; positivity

theorem rowOk_sound {L : VG.Proof.Divstep.LinMap} {r1 r2 d : VG.Proof.Divstep.Row} (h : VG.Proof.Divstep.rowOk L r1 r2 d = true) {x y : ℚ}
    (h1 : (r1.1 : ℚ) * x + r1.2.1 * y ≤ r1.2.2) (h2 : (r2.1 : ℚ) * x + r2.2.1 * y ≤ r2.2.2) :
    (d.1 : ℚ) * L.fx x y + d.2.1 * L.fy x y ≤ d.2.2 := by
  obtain ⟨a1, b1, c1⟩ := r1
  obtain ⟨a2, b2, c2⟩ := r2
  obtain ⟨g, hh, c⟩ := d
  simp only at h1 h2 ⊢
  have hq := L.q_pos
  have hsd := VG.Proof.Divstep.sd_pow_pos L.k
  -- The target row in terms of `G x + H y`.
  have key : (g : ℚ) * L.fx x y + hh * L.fy x y =
      (((g * L.a00 + hh * L.a10 : Int) : ℚ) * x + ((g * L.a01 + hh * L.a11 : Int) : ℚ) * y) / L.q := by
    unfold LinMap.fx LinMap.fy; push_cast; field_simp; ring
  rw [key, div_le_iff₀ hq]
  simp only [VG.Proof.Divstep.rowOk] at h
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
  have eq : (c : ℚ) * L.q * D = ((c : ℚ) * 2 ^ L.e * (VG.Proof.Divstep.sn : ℚ) ^ L.k * D) / (VG.Proof.Divstep.sd : ℚ) ^ L.k := by
    unfold LinMap.q; rw [VG.Proof.Divstep.s_pow]; field_simp
  split at h
  · rename_i hDp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hMp, hNp⟩, hl⟩ := h
    have hDq : (0 : ℚ) < D := by exact_mod_cast hDp
    have hMq : (0 : ℚ) ≤ Mn := by exact_mod_cast hMp
    have hNq : (0 : ℚ) ≤ Nn := by exact_mod_cast hNp
    have hlq : ((Mn : ℚ) * c1 + Nn * c2) * (VG.Proof.Divstep.sd : ℚ) ^ L.k ≤ (c : ℚ) * 2 ^ L.e * (VG.Proof.Divstep.sn : ℚ) ^ L.k * D := by
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
    have hlq : (c : ℚ) * 2 ^ L.e * (VG.Proof.Divstep.sn : ℚ) ^ L.k * D ≤ ((Mn : ℚ) * c1 + Nn * c2) * (VG.Proof.Divstep.sd : ℚ) ^ L.k := by
      exact_mod_cast hl
    have s1 := mul_le_mul_of_nonpos_left h1 hMq
    have s2 := mul_le_mul_of_nonpos_left h2 hNq
    have h3 : c * L.q * D ≤ (Mn : ℚ) * c1 + Nn * c2 := by rw [eq, div_le_iff₀ hsd]; exact hlq
    have hle : (-D : ℚ) * ((G : ℚ) * x + H * y) ≤ (-D) * (c * L.q) := by
      have := comb; nlinarith
    exact le_of_mul_le_mul_left hle (by linarith)

theorem getD_row {P : List VG.Proof.Divstep.Row} {x y : ℚ} (h : VG.Proof.Divstep.inP P x y) (i : Nat) :
    ((P.getD i (0, 0, 0)).1 : ℚ) * x + (P.getD i (0, 0, 0)).2.1 * y ≤ (P.getD i (0, 0, 0)).2.2 := by
  rw [List.getD_eq_getElem?_getD]
  cases hP : P[i]? with
  | none => simp
  | some r => exact h r (List.mem_of_getElem? hP)

theorem inclOk_sound {L : VG.Proof.Divstep.LinMap} {src : List VG.Proof.Divstep.Row} :
    ∀ (dst : List VG.Proof.Divstep.Row) (cert : List (Nat × Nat)), VG.Proof.Divstep.inclOk L src dst cert = true →
      ∀ x y, VG.Proof.Divstep.inP src x y → VG.Proof.Divstep.inP dst (L.fx x y) (L.fy x y)
  | [], [], _, _, _, _ => fun _ h => absurd h List.not_mem_nil
  | d :: ds, (i, j) :: cs, h, x, y, hs => by
    simp only [VG.Proof.Divstep.inclOk, Bool.and_eq_true] at h
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact VG.Proof.Divstep.rowOk_sound h.1 (VG.Proof.Divstep.getD_row hs i) (VG.Proof.Divstep.getD_row hs j)
    · exact VG.Proof.Divstep.inclOk_sound ds cs h.2 x y hs r hr
  | [], _ :: _, h, _, _, _ => by simp [VG.Proof.Divstep.inclOk] at h
  | _ :: _, [], h, _, _, _ => by simp [VG.Proof.Divstep.inclOk] at h

/-- A checked inclusion: its map sends its source into its target. -/
theorem Incl.ok_sound {I : VG.Proof.Divstep.Incl} (h : I.ok = true) {x y : ℚ} (hs : VG.Proof.Divstep.inP I.src x y) :
    VG.Proof.Divstep.inP I.dst (I.map.fx x y) (I.map.fy x y) :=
  VG.Proof.Divstep.inclOk_sound I.dst I.cert h x y hs

end VG.Proof.Divstep

end

/- Proofs formerly in `VerifiedGarbage.Proof.Divstep.HullData`. -/
section

/-!
# The hulls of the divstep bound: data

Bernstein's `hull-light` polygons (D. J. Bernstein, `hull-light-20230416.sage`,
as generated into J. Harrison's HOL Light `Divstep/hull_light.ml`, approximate
build), each a list of rows `(a, b, c)` meaning `a x + b y ≤ c`, counterclockwise:
`H1` (`δ = 1/2`) and `H0` (`δ = -1/2`), 80 edges each; the starting triangle
`Hinit` (`0 ≤ y ≤ x ≤ 1`) and the bounding box `Houter`. The inclusions between
them (`incl*`), as linear maps `(x, y) ↦ A (x, y) / (2^e s^k)` and, for every
row of the target, the two rows of the source whose Farkas combination bounds it.
-/

namespace VG.Proof.Divstep

/-- `H0` of `hull_light.ml`. -/
def H0 : List VG.Proof.Divstep.Row := [
  (-413007872, -32178176, 275907781),
  (-32309248, -6881280, 21583161),
  (-137199616, -37961728, 91847345),
  (-27099136, -7733248, 18176645),
  (-68321280, -23134208, 46464197),
  (-26869760, -10027008, 18466107),
  (-52412416, -19972096, 36108393),
  (-7979008, -3162112, 5552625),
  (-121733120, -53051392, 86950107),
  (-124731392, -66289664, 95315653),
  (-165806080, -105447424, 137755571),
  (-22740992, -15466496, 19572823),
  (-3604480, -2555904, 3177943),
  (-5537792, -5177344, 5799491),
  (-289406976, -340459520, 355053887),
  (-2048000, -2605056, 2671329),
  (-26116096, -42532864, 41635449),
  (-66748416, -154992640, 144601685),
  (-3899392, -17530880, 15704445),
  (-65536, -91619328, 79611463),
  (9371648, -118292480, 101844089),
  (753664, -5898240, 5057377),
  (129499136, -923729920, 791274703),
  (1130496, -7061504, 6069771),
  (481280, -1114112, 1004531),
  (44220416, -66781184, 62719715),
  (75169792, -86212608, 85043005),
  (113278976, -111640576, 116276001),
  (11419648, -10895360, 11507295),
  (4050944, -3178496, 3679349),
  (13631488, -9502720, 11699263),
  (540934144, -365101056, 457442411),
  (8454144, -5439488, 7031327),
  (34471936, -19202048, 27364823),
  (20946944, -9748480, 15848215),
  (24879104, -8986624, 18073405),
  (131072, -32768, 92351),
  (191823872, -40435712, 133937273),
  (9568256, -1769472, 6651805),
  (5767168, -196608, 3914969),
  (413007872, 32178176, 275907781),
  (32309248, 6881280, 21583161),
  (137199616, 37961728, 91847345),
  (27099136, 7733248, 18176645),
  (68321280, 23134208, 46464197),
  (26869760, 10027008, 18466107),
  (52412416, 19972096, 36108393),
  (7979008, 3162112, 5552625),
  (121733120, 53051392, 86950107),
  (124731392, 66289664, 95315653),
  (165806080, 105447424, 137755571),
  (22740992, 15466496, 19572823),
  (3604480, 2555904, 3177943),
  (5537792, 5177344, 5799491),
  (289406976, 340459520, 355053887),
  (2048000, 2605056, 2671329),
  (26116096, 42532864, 41635449),
  (66748416, 154992640, 144601685),
  (3899392, 17530880, 15704445),
  (65536, 91619328, 79611463),
  (-9371648, 118292480, 101844089),
  (-753664, 5898240, 5057377),
  (-129499136, 923729920, 791274703),
  (-1130496, 7061504, 6069771),
  (-481280, 1114112, 1004531),
  (-44220416, 66781184, 62719715),
  (-75169792, 86212608, 85043005),
  (-113278976, 111640576, 116276001),
  (-11419648, 10895360, 11507295),
  (-4050944, 3178496, 3679349),
  (-13631488, 9502720, 11699263),
  (-540934144, 365101056, 457442411),
  (-8454144, 5439488, 7031327),
  (-34471936, 19202048, 27364823),
  (-20946944, 9748480, 15848215),
  (-24879104, 8986624, 18073405),
  (-131072, 32768, 92351),
  (-191823872, 40435712, 133937273),
  (-9568256, 1769472, 6651805),
  (-5767168, 196608, 3914969)]

/-- `H1` of `hull_light.ml`. -/
def H1 : List VG.Proof.Divstep.Row := [
  (-5865472, -950272, 6035371),
  (-439386112, -185892864, 480443643),
  (-49741824, -27000832, 57079641),
  (-33521664, -25640960, 41914863),
  (-1867776, -1490944, 2368161),
  (-7634944, -7815168, 10605687),
  (-950272, -1130496, 1407123),
  (-438239232, -539754496, 659132513),
  (-13041664, -17039360, 20256657),
  (-7733248, -11943936, 13225515),
  (-897024, -2035712, 1977153),
  (-1275904, -4450304, 3928715),
  (-2211840, -9404416, 8039969),
  (-7733248, -38076416, 31944087),
  (-1966080, -55902208, 42311631),
  (11730944, -156696576, 110400449),
  (22740992, -117506048, 77682557),
  (166330368, -684523520, 441063407),
  (33882112, -135659520, 87245513),
  (50659328, -175046656, 111549985),
  (11010048, -34930688, 22163375),
  (145883136, -455802880, 288985723),
  (3457024, -10452992, 6651805),
  (58130432, -162430976, 104374325),
  (290521088, -691929088, 457690221),
  (14442496, -29925376, 20669487),
  (19062784, -37560320, 26430931),
  (15433728, -29458432, 21015329),
  (5660672, -8896512, 6951751),
  (373096448, -503644160, 426281637),
  (5701632, -7340032, 6407825),
  (46596096, -51871744, 49963991),
  (84901888, -79036416, 86789633),
  (134447104, -97124352, 131957561),
  (100401152, -50266112, 95584823),
  (64782336, -27295744, 61112343),
  (12943360, -4784128, 12157023),
  (1012072448, -364183552, 949861697),
  (3866624, -1310720, 3642043),
  (39124992, -2621440, 38657149),
  (5865472, 950272, 6035371),
  (439386112, 185892864, 480443643),
  (49741824, 27000832, 57079641),
  (33521664, 25640960, 41914863),
  (1867776, 1490944, 2368161),
  (7634944, 7815168, 10605687),
  (950272, 1130496, 1407123),
  (438239232, 539754496, 659132513),
  (13041664, 17039360, 20256657),
  (7733248, 11943936, 13225515),
  (897024, 2035712, 1977153),
  (1275904, 4450304, 3928715),
  (2211840, 9404416, 8039969),
  (7733248, 38076416, 31944087),
  (1966080, 55902208, 42311631),
  (-11730944, 156696576, 110400449),
  (-22740992, 117506048, 77682557),
  (-166330368, 684523520, 441063407),
  (-33882112, 135659520, 87245513),
  (-50659328, 175046656, 111549985),
  (-11010048, 34930688, 22163375),
  (-145883136, 455802880, 288985723),
  (-3457024, 10452992, 6651805),
  (-58130432, 162430976, 104374325),
  (-290521088, 691929088, 457690221),
  (-14442496, 29925376, 20669487),
  (-19062784, 37560320, 26430931),
  (-15433728, 29458432, 21015329),
  (-5660672, 8896512, 6951751),
  (-373096448, 503644160, 426281637),
  (-5701632, 7340032, 6407825),
  (-46596096, 51871744, 49963991),
  (-84901888, 79036416, 86789633),
  (-134447104, 97124352, 131957561),
  (-100401152, 50266112, 95584823),
  (-64782336, 27295744, 61112343),
  (-12943360, 4784128, 12157023),
  (-1012072448, 364183552, 949861697),
  (-3866624, 1310720, 3642043),
  (-39124992, 2621440, 38657149)]

/-- `hinit_0_1` of `hull_light.ml`. -/
def Hinit : List VG.Proof.Divstep.Row := [
  (0, -1, 0),
  (1, 0, 1),
  (-1, 1, 0)]

/-- `Houter` of `hull_light.ml`. -/
def Houter : List VG.Proof.Divstep.Row := [
  (0, -512, 379),
  (8192, 0, 8193),
  (0, 512, 379),
  (-8192, 0, 8193)]

/-- `init2stable`: `hinit_0_1 → H1` by `[['2753/4096', '0'], ['0', '2753/4096']]`, `k = 0`. -/
def inclInit : VG.Proof.Divstep.Incl where
  map := ⟨2753, 0, 0, 2753, 12, 0⟩
  src := VG.Proof.Divstep.Hinit
  dst := VG.Proof.Divstep.H1
  cert := [(2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (1, 2), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0), (2, 0)]

/-- `theoremouter`: `H1 → Houter` by `[['1', '0'], ['0', '1']]`, `k = 0`. -/
def inclOuter : VG.Proof.Divstep.Incl where
  map := ⟨1, 0, 0, 1, 0, 0⟩
  src := VG.Proof.Divstep.H1
  dst := VG.Proof.Divstep.Houter
  cert := [(14, 15), (39, 40), (54, 55), (79, 0)]

/-- `theorem0`: `H0 → H1` by `[['1', '0'], ['0', '1/2']]`, `k = 1`. -/
def incl0 : VG.Proof.Divstep.Incl where
  map := ⟨2, 0, 0, 1, 1, 1⟩
  src := VG.Proof.Divstep.H0
  dst := VG.Proof.Divstep.H1
  cert := [(0, 1), (0, 1), (1, 2), (6, 7), (7, 8), (8, 9), (9, 10), (9, 10), (10, 11), (12, 13), (13, 14), (16, 17), (16, 17), (17, 18), (18, 19), (22, 23), (23, 24), (24, 25), (24, 25), (24, 25), (24, 25), (24, 25), (24, 25), (25, 26), (25, 26), (26, 27), (27, 28), (27, 28), (28, 29), (30, 31), (31, 32), (33, 34), (33, 34), (35, 36), (35, 36), (37, 38), (38, 39), (38, 39), (38, 39), (39, 40), (40, 41), (40, 41), (41, 42), (46, 47), (47, 48), (48, 49), (49, 50), (49, 50), (50, 51), (52, 53), (53, 54), (56, 57), (56, 57), (57, 58), (58, 59), (62, 63), (63, 64), (64, 65), (64, 65), (64, 65), (64, 65), (64, 65), (64, 65), (65, 66), (65, 66), (66, 67), (67, 68), (67, 68), (68, 69), (70, 71), (71, 72), (73, 74), (73, 74), (75, 76), (75, 76), (77, 78), (78, 79), (78, 79), (78, 79), (79, 0)]

/-- `theorem1`: `H0 → H1` by `[['1', '0'], ['1/2', '1/2']]`, `k = 1`. -/
def incl1 : VG.Proof.Divstep.Incl where
  map := ⟨2, 0, 1, 1, 1, 1⟩
  src := VG.Proof.Divstep.H0
  dst := VG.Proof.Divstep.H1
  cert := [(79, 0), (0, 1), (1, 2), (1, 2), (2, 3), (3, 4), (4, 5), (6, 7), (6, 7), (7, 8), (9, 10), (9, 10), (10, 11), (12, 13), (12, 13), (13, 14), (16, 17), (16, 17), (16, 17), (17, 18), (17, 18), (17, 18), (17, 18), (17, 18), (18, 19), (18, 19), (19, 20), (19, 20), (23, 24), (24, 25), (24, 25), (25, 26), (28, 29), (32, 33), (35, 36), (35, 36), (36, 37), (36, 37), (37, 38), (38, 39), (39, 40), (40, 41), (41, 42), (41, 42), (42, 43), (43, 44), (44, 45), (46, 47), (46, 47), (47, 48), (49, 50), (49, 50), (50, 51), (52, 53), (52, 53), (53, 54), (56, 57), (56, 57), (56, 57), (57, 58), (57, 58), (57, 58), (57, 58), (57, 58), (58, 59), (58, 59), (59, 60), (59, 60), (63, 64), (64, 65), (64, 65), (65, 66), (68, 69), (72, 73), (75, 76), (75, 76), (76, 77), (76, 77), (77, 78), (78, 79)]

/-- `theorem3`: `H1 → H1` by `[['0', '1'], ['-1/2', '1/2']]`, `k = 1`. -/
def incl3 : VG.Proof.Divstep.Incl where
  map := ⟨0, 2, -1, 1, 1, 1⟩
  src := VG.Proof.Divstep.H1
  dst := VG.Proof.Divstep.H1
  cert := [(15, 16), (15, 16), (16, 17), (18, 19), (18, 19), (22, 23), (23, 24), (23, 24), (23, 24), (24, 25), (27, 28), (27, 28), (28, 29), (28, 29), (31, 32), (32, 33), (33, 34), (33, 34), (34, 35), (35, 36), (36, 37), (36, 37), (38, 39), (38, 39), (38, 39), (39, 40), (39, 40), (39, 40), (40, 41), (41, 42), (42, 43), (43, 44), (45, 46), (49, 50), (50, 51), (51, 52), (52, 53), (52, 53), (52, 53), (54, 55), (55, 56), (55, 56), (56, 57), (58, 59), (58, 59), (62, 63), (63, 64), (63, 64), (63, 64), (64, 65), (67, 68), (67, 68), (68, 69), (68, 69), (71, 72), (72, 73), (73, 74), (73, 74), (74, 75), (75, 76), (76, 77), (76, 77), (78, 79), (78, 79), (78, 79), (79, 0), (79, 0), (79, 0), (0, 1), (1, 2), (2, 3), (3, 4), (5, 6), (9, 10), (10, 11), (11, 12), (12, 13), (12, 13), (12, 13), (14, 15)]

/-- `theorem5`: `H1 → H0` by `[['0', '1/2'], ['-1/2', '1/4']]`, `k = 2`. -/
def incl5 : VG.Proof.Divstep.Incl where
  map := ⟨0, 2, -2, 1, 2, 2⟩
  src := VG.Proof.Divstep.H1
  dst := VG.Proof.Divstep.H0
  cert := [(15, 16), (15, 16), (17, 18), (17, 18), (19, 20), (19, 20), (21, 22), (22, 23), (22, 23), (24, 25), (24, 25), (26, 27), (26, 27), (28, 29), (28, 29), (30, 31), (30, 31), (32, 33), (32, 33), (33, 34), (35, 36), (35, 36), (37, 38), (37, 38), (38, 39), (40, 41), (40, 41), (41, 42), (42, 43), (43, 44), (44, 45), (44, 45), (45, 46), (47, 48), (49, 50), (49, 50), (51, 52), (51, 52), (52, 53), (54, 55), (55, 56), (55, 56), (57, 58), (57, 58), (59, 60), (59, 60), (61, 62), (62, 63), (62, 63), (64, 65), (64, 65), (66, 67), (66, 67), (68, 69), (68, 69), (70, 71), (70, 71), (72, 73), (72, 73), (73, 74), (75, 76), (75, 76), (77, 78), (77, 78), (78, 79), (0, 1), (0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (4, 5), (5, 6), (7, 8), (9, 10), (9, 10), (11, 12), (11, 12), (12, 13), (14, 15)]

/-- `theorem_2`: `H1 → H0` by `[['0', '1/4'], ['-1/4', '1/16']]`, `k = 4`. -/
def inclN2 : VG.Proof.Divstep.Incl where
  map := ⟨0, 4, -4, 1, 4, 4⟩
  src := VG.Proof.Divstep.H1
  dst := VG.Proof.Divstep.H0
  cert := [(15, 16), (16, 17), (18, 19), (18, 19), (19, 20), (22, 23), (22, 23), (23, 24), (23, 24), (24, 25), (27, 28), (27, 28), (27, 28), (29, 30), (31, 32), (31, 32), (32, 33), (33, 34), (34, 35), (38, 39), (38, 39), (38, 39), (38, 39), (38, 39), (40, 41), (40, 41), (42, 43), (42, 43), (43, 44), (45, 46), (45, 46), (46, 47), (47, 48), (49, 50), (49, 50), (50, 51), (51, 52), (52, 53), (53, 54), (54, 55), (55, 56), (56, 57), (58, 59), (58, 59), (59, 60), (62, 63), (62, 63), (63, 64), (63, 64), (64, 65), (67, 68), (67, 68), (67, 68), (69, 70), (71, 72), (71, 72), (72, 73), (73, 74), (74, 75), (78, 79), (78, 79), (78, 79), (78, 79), (78, 79), (0, 1), (0, 1), (2, 3), (2, 3), (3, 4), (5, 6), (5, 6), (6, 7), (7, 8), (9, 10), (9, 10), (10, 11), (11, 12), (12, 13), (13, 14), (14, 15)]

/-- `theorem_1`: `H1 → H0` by `[['0', '1/4'], ['-1/4', '3/16']]`, `k = 4`. -/
def inclN1 : VG.Proof.Divstep.Incl where
  map := ⟨0, 4, -4, 3, 4, 4⟩
  src := VG.Proof.Divstep.H1
  dst := VG.Proof.Divstep.H0
  cert := [(14, 15), (15, 16), (16, 17), (16, 17), (18, 19), (19, 20), (19, 20), (19, 20), (21, 22), (23, 24), (24, 25), (24, 25), (24, 25), (27, 28), (27, 28), (28, 29), (28, 29), (30, 31), (31, 32), (32, 33), (33, 34), (33, 34), (33, 34), (33, 34), (38, 39), (38, 39), (39, 40), (40, 41), (40, 41), (41, 42), (42, 43), (42, 43), (44, 45), (45, 46), (48, 49), (49, 50), (50, 51), (51, 52), (52, 53), (54, 55), (54, 55), (55, 56), (56, 57), (56, 57), (58, 59), (59, 60), (59, 60), (59, 60), (61, 62), (63, 64), (64, 65), (64, 65), (64, 65), (67, 68), (67, 68), (68, 69), (68, 69), (70, 71), (71, 72), (72, 73), (73, 74), (73, 74), (73, 74), (73, 74), (78, 79), (78, 79), (79, 0), (0, 1), (0, 1), (1, 2), (2, 3), (2, 3), (4, 5), (5, 6), (8, 9), (9, 10), (10, 11), (11, 12), (12, 13), (14, 15)]

/-- `theorem_4scale`: `H1 → H1` by `[['33/64', '33/512'], ['0', '33/64']]`, `k = 2`. -/
def inclN4scale : VG.Proof.Divstep.Incl where
  map := ⟨264, 33, 0, 264, 9, 2⟩
  src := VG.Proof.Divstep.H1
  dst := VG.Proof.Divstep.H1
  cert := [(0, 1), (2, 3), (2, 3), (4, 5), (4, 5), (5, 6), (8, 9), (8, 9), (8, 9), (9, 10), (10, 11), (11, 12), (12, 13), (13, 14), (14, 15), (15, 16), (16, 17), (18, 19), (18, 19), (19, 20), (21, 22), (22, 23), (22, 23), (23, 24), (24, 25), (26, 27), (27, 28), (27, 28), (28, 29), (30, 31), (30, 31), (31, 32), (32, 33), (33, 34), (35, 36), (38, 39), (38, 39), (38, 39), (38, 39), (39, 40), (40, 41), (42, 43), (42, 43), (44, 45), (44, 45), (45, 46), (48, 49), (48, 49), (48, 49), (49, 50), (50, 51), (51, 52), (52, 53), (53, 54), (54, 55), (55, 56), (56, 57), (58, 59), (58, 59), (59, 60), (61, 62), (62, 63), (62, 63), (63, 64), (64, 65), (66, 67), (67, 68), (67, 68), (68, 69), (70, 71), (70, 71), (71, 72), (72, 73), (73, 74), (75, 76), (78, 79), (78, 79), (78, 79), (78, 79), (79, 0)]

/-- `theorem_3scale`: `H1 → H1` by `[['33/64', '-33/512'], ['0', '33/64']]`, `k = 2`. -/
def inclN3scale : VG.Proof.Divstep.Incl where
  map := ⟨264, -33, 0, 264, 9, 2⟩
  src := VG.Proof.Divstep.H1
  dst := VG.Proof.Divstep.H1
  cert := [(79, 0), (0, 1), (0, 1), (2, 3), (2, 3), (4, 5), (5, 6), (5, 6), (5, 6), (8, 9), (9, 10), (10, 11), (11, 12), (12, 13), (13, 14), (14, 15), (15, 16), (16, 17), (16, 17), (18, 19), (19, 20), (19, 20), (20, 21), (22, 23), (23, 24), (24, 25), (24, 25), (25, 26), (27, 28), (28, 29), (28, 29), (30, 31), (31, 32), (32, 33), (33, 34), (33, 34), (34, 35), (34, 35), (34, 35), (38, 39), (39, 40), (40, 41), (40, 41), (42, 43), (42, 43), (44, 45), (45, 46), (45, 46), (45, 46), (48, 49), (49, 50), (50, 51), (51, 52), (52, 53), (53, 54), (54, 55), (55, 56), (56, 57), (56, 57), (58, 59), (59, 60), (59, 60), (60, 61), (62, 63), (63, 64), (64, 65), (64, 65), (65, 66), (67, 68), (68, 69), (68, 69), (70, 71), (71, 72), (72, 73), (73, 74), (73, 74), (74, 75), (74, 75), (74, 75), (78, 79)]

end VG.Proof.Divstep

end

/- Proofs formerly in `VerifiedGarbage.Proof.Divstep.Incl`. -/
section

/-!
# The hulls of the divstep bound: the inclusions

Each of the ten inclusions between the hulls, checked by the kernel
(`Incl.ok`, sound by `Incl.ok_sound`).
-/

namespace VG.Proof.Divstep

theorem inclInit_ok : inclInit.ok = true := by decide +kernel
theorem inclOuter_ok : inclOuter.ok = true := by decide +kernel
theorem incl0_ok : incl0.ok = true := by decide +kernel
theorem incl1_ok : incl1.ok = true := by decide +kernel
theorem incl3_ok : incl3.ok = true := by decide +kernel
theorem incl5_ok : incl5.ok = true := by decide +kernel
theorem inclN2_ok : inclN2.ok = true := by decide +kernel
theorem inclN1_ok : inclN1.ok = true := by decide +kernel
theorem inclN4scale_ok : inclN4scale.ok = true := by decide +kernel
theorem inclN3scale_ok : inclN3scale.ok = true := by decide +kernel

end VG.Proof.Divstep

end

/- Proofs formerly in `VerifiedGarbage.Proof.Divstep.Hull`. -/
section

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
abbrev H1P (x y : ℚ) : Prop := VG.Proof.Divstep.inP VG.Proof.Divstep.H1 x y
/-- `H0` holds `(x, y)`. -/
abbrev H0P (x y : ℚ) : Prop := VG.Proof.Divstep.inP VG.Proof.Divstep.H0 x y

theorem inP_congr {P : List VG.Proof.Divstep.Row} {x y x' y' : ℚ} (h : VG.Proof.Divstep.inP P x y) (hx : x = x') (hy : y = y') :
    VG.Proof.Divstep.inP P x' y' := hx ▸ hy ▸ h

/-- A polygon is convex. -/
theorem inP_convex {P : List VG.Proof.Divstep.Row} {x₁ y₁ x₂ y₂ t : ℚ} (h₁ : VG.Proof.Divstep.inP P x₁ y₁) (h₂ : VG.Proof.Divstep.inP P x₂ y₂)
    (ht : 0 ≤ t) (ht' : t ≤ 1) : VG.Proof.Divstep.inP P (t * x₁ + (1 - t) * x₂) (t * y₁ + (1 - t) * y₂) := by
  intro r hr
  have a := mul_le_mul_of_nonneg_left (h₁ r hr) ht
  have b := mul_le_mul_of_nonneg_left (h₂ r hr) (by linarith : (0 : ℚ) ≤ 1 - t)
  nlinarith

theorem H1_zero : VG.Proof.Divstep.H1P 0 0 := by
  have : H1.all (fun r => decide (0 ≤ r.2.2)) = true := by decide +kernel
  intro r hr
  have := List.all_eq_true.mp this r hr
  simp only [decide_eq_true_eq] at this
  simp only [mul_zero, add_zero]
  exact_mod_cast this

/-- `H1` scaled towards its origin. -/
theorem H1_shrink {x y t : ℚ} (h : VG.Proof.Divstep.H1P x y) (ht : 0 ≤ t) (ht' : t ≤ 1) : VG.Proof.Divstep.H1P (t * x) (t * y) :=
  VG.Proof.Divstep.inP_congr (VG.Proof.Divstep.inP_convex h VG.Proof.Divstep.H1_zero ht ht') (by ring) (by ring)

/-- `H1` lies in the box `|x| ≤ 8193/8192`, `|y| ≤ 379/512`. -/
theorem H1_box {x y : ℚ} (h : VG.Proof.Divstep.H1P x y) : |x| ≤ 8193 / 8192 ∧ |y| ≤ 379 / 512 := by
  have o := Incl.ok_sound VG.Proof.Divstep.inclOuter_ok (x := x) (y := y) h
  simp only [VG.Proof.Divstep.inclOuter, LinMap.fx, LinMap.fy, LinMap.q, pow_zero, mul_one] at o
  have r1 := o (0, -512, 379) (by simp [VG.Proof.Divstep.Houter])
  have r2 := o (8192, 0, 8193) (by simp [VG.Proof.Divstep.Houter])
  have r3 := o (0, 512, 379) (by simp [VG.Proof.Divstep.Houter])
  have r4 := o (-8192, 0, 8193) (by simp [VG.Proof.Divstep.Houter])
  push_cast at r1 r2 r3 r4
  constructor <;> rw [abs_le] <;> constructor <;> linarith

/-- An inclusion, with its map's coordinates computed. -/
theorem incl_at {I : VG.Proof.Divstep.Incl} (h : I.ok = true) {x y x' y' : ℚ} (hs : VG.Proof.Divstep.inP I.src x y)
    (hx : I.map.fx x y = x') (hy : I.map.fy x y = y') : VG.Proof.Divstep.inP I.dst x' y' :=
  hx ▸ hy ▸ Incl.ok_sound h hs

theorem s_ne : VG.Proof.Divstep.s ≠ 0 := ne_of_gt VG.Proof.Divstep.s_pos

theorem ite_t {α : Sort _} {c : Prop} [Decidable c] (h : c) {x y : α} : (if c then x else y) = x := by
  simp [h]

theorem ite_f {α : Sort _} {c : Prop} [Decidable c] (h : ¬c) {x y : α} : (if c then x else y) = y := by
  simp [h]

/-- The fudge factor `32/33` of the scaled polygons. -/
abbrev c32 : ℚ := 32 / 33

/-- `H1` holds `((X/2 ± Y/16) / s², (Y/2) / s²)` with `(X, Y)`. -/
theorem H1_16 {X Y : ℚ} (h : VG.Proof.Divstep.H1P X Y) :
    VG.Proof.Divstep.H1P ((X / 2 + Y / 16) / VG.Proof.Divstep.s ^ 2) ((Y / 2) / VG.Proof.Divstep.s ^ 2) ∧ VG.Proof.Divstep.H1P ((X / 2 - Y / 16) / VG.Proof.Divstep.s ^ 2) ((Y / 2) / VG.Proof.Divstep.s ^ 2) := by
  have hs := VG.Proof.Divstep.s_ne
  constructor
  · have a := VG.Proof.Divstep.incl_at VG.Proof.Divstep.inclN4scale_ok (x := X) (y := Y) (by exact h) rfl rfl
    refine VG.Proof.Divstep.inP_congr (VG.Proof.Divstep.H1_shrink a (t := VG.Proof.Divstep.c32) (by norm_num) (by norm_num)) ?_ ?_ <;>
      simp only [VG.Proof.Divstep.inclN4scale, LinMap.fx, LinMap.fy, LinMap.q] <;> push_cast <;> field_simp <;> ring
  · have a := VG.Proof.Divstep.incl_at VG.Proof.Divstep.inclN3scale_ok (x := X) (y := Y) (by exact h) rfl rfl
    refine VG.Proof.Divstep.inP_congr (VG.Proof.Divstep.H1_shrink a (t := VG.Proof.Divstep.c32) (by norm_num) (by norm_num)) ?_ ?_ <;>
      simp only [VG.Proof.Divstep.inclN3scale, LinMap.fx, LinMap.fy, LinMap.q] <;> push_cast <;> field_simp <;> ring

/-- `H1` holds `((X/2 ± Y/2^(m+2)) / s², (Y/2) / s²)` with `(X, Y)`, for
`m ≥ 2`: a combination of the two of `H1_16` along the same `y`. -/
theorem H1_shear {X Y : ℚ} (h : VG.Proof.Divstep.H1P X Y) {m : Nat} (hm : 2 ≤ m) :
    VG.Proof.Divstep.H1P ((X / 2 + Y / 2 ^ (m + 2)) / VG.Proof.Divstep.s ^ 2) ((Y / 2) / VG.Proof.Divstep.s ^ 2) ∧
      VG.Proof.Divstep.H1P ((X / 2 - Y / 2 ^ (m + 2)) / VG.Proof.Divstep.s ^ 2) ((Y / 2) / VG.Proof.Divstep.s ^ 2) := by
  obtain ⟨a, b⟩ := VG.Proof.Divstep.H1_16 h
  have hs := VG.Proof.Divstep.s_ne
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
  · refine VG.Proof.Divstep.inP_congr (VG.Proof.Divstep.inP_convex a b t0 t1) ?_ ?_ <;> (try rw [e]) <;> field_simp <;> ring
  · refine VG.Proof.Divstep.inP_congr (VG.Proof.Divstep.inP_convex a b u0 u1) ?_ ?_ <;> (try rw [e]) <;> field_simp <;> ring

/-! ## The polygons `W i` -/

/-- `W i` for `i = n ≥ 0`. -/
def Wpos (n : Nat) (x y : ℚ) : Prop :=
  if n ≤ 2 then VG.Proof.Divstep.H1P (x * VG.Proof.Divstep.s ^ n) (y * (2 * VG.Proof.Divstep.s) ^ n) else VG.Proof.Divstep.H1P (VG.Proof.Divstep.c32 * x * VG.Proof.Divstep.s ^ n) (VG.Proof.Divstep.c32 * y * (2 * VG.Proof.Divstep.s) ^ n)

/-- `W i` for `i = -j ≤ -1`. -/
def Wneg (j : Nat) (x y : ℚ) : Prop :=
  if j = 1 then VG.Proof.Divstep.H0P x y
  else if j = 2 then VG.Proof.Divstep.H1P ((x - 2 * y) * VG.Proof.Divstep.s ^ 3) (4 * x * VG.Proof.Divstep.s ^ 3)
  else VG.Proof.Divstep.H1P (VG.Proof.Divstep.c32 * (x - 2 * y) * VG.Proof.Divstep.s ^ (j + 1)) (VG.Proof.Divstep.c32 * x * VG.Proof.Divstep.s ^ (j + 1) * 2 ^ j)

/-- The polygon of `i = δ - 1/2`. -/
def W (i : Int) (x y : ℚ) : Prop := if 0 ≤ i then VG.Proof.Divstep.Wpos i.toNat x y else VG.Proof.Divstep.Wneg (-i).toNat x y

/-- An even step from `i ≥ 0`. -/
theorem Wpos_even {n : Nat} {x y : ℚ} (h : VG.Proof.Divstep.Wpos n x y) : VG.Proof.Divstep.Wpos (n + 1) (x / VG.Proof.Divstep.s) (y / (2 * VG.Proof.Divstep.s)) := by
  have hs := VG.Proof.Divstep.s_ne
  unfold VG.Proof.Divstep.Wpos at h ⊢
  rcases Nat.lt_or_ge n 2 with hn | hn
  · simp (disch := omega) only [VG.Proof.Divstep.ite_t] at h ⊢
    refine VG.Proof.Divstep.inP_congr h ?_ ?_ <;> rw [pow_succ] <;> field_simp
  · rcases Nat.lt_or_ge n 3 with hn' | hn'
    · obtain rfl : n = 2 := by omega
      simp (disch := omega) only [VG.Proof.Divstep.ite_t] at h; simp (disch := omega) only [VG.Proof.Divstep.ite_f]
      refine VG.Proof.Divstep.inP_congr (VG.Proof.Divstep.H1_shrink h (t := VG.Proof.Divstep.c32) (by norm_num) (by norm_num)) ?_ ?_ <;> first | (field_simp; done) | (field_simp; ring)
    · simp (disch := omega) only [VG.Proof.Divstep.ite_f] at h ⊢
      refine VG.Proof.Divstep.inP_congr h ?_ ?_ <;> rw [pow_succ] <;> field_simp

/-- An odd step from `i ≥ 0`: the swap, to `i = -n`. -/
theorem Wpos_odd {n : Nat} {x y : ℚ} (h : VG.Proof.Divstep.Wpos n x y) :
    (n = 0 → VG.Proof.Divstep.Wpos 0 (y / VG.Proof.Divstep.s) ((y - x) / (2 * VG.Proof.Divstep.s))) ∧ (1 ≤ n → VG.Proof.Divstep.Wneg n (y / VG.Proof.Divstep.s) ((y - x) / (2 * VG.Proof.Divstep.s))) := by
  have hs := VG.Proof.Divstep.s_ne
  unfold VG.Proof.Divstep.Wpos at h
  refine ⟨fun hn => ?_, fun hn => ?_⟩
  · subst hn
    simp (disch := omega) only [VG.Proof.Divstep.ite_t, pow_zero, mul_one] at h
    unfold VG.Proof.Divstep.Wpos
    simp (disch := omega) only [VG.Proof.Divstep.ite_t, pow_zero, mul_one]
    refine VG.Proof.Divstep.incl_at VG.Proof.Divstep.incl3_ok (x := x) (y := y) (by exact h) ?_ ?_ <;>
      simp only [VG.Proof.Divstep.incl3, LinMap.fx, LinMap.fy, LinMap.q] <;> push_cast <;> field_simp <;> ring
  · unfold VG.Proof.Divstep.Wneg
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · obtain rfl : n = 1 := by omega
      simp (disch := omega) only [VG.Proof.Divstep.ite_t, pow_one] at h ⊢
      refine VG.Proof.Divstep.incl_at VG.Proof.Divstep.incl5_ok (x := x * VG.Proof.Divstep.s) (y := y * (2 * VG.Proof.Divstep.s)) (by exact h) ?_ ?_ <;>
        simp only [VG.Proof.Divstep.incl5, LinMap.fx, LinMap.fy, LinMap.q] <;> push_cast <;> field_simp <;> ring
    · rcases Nat.lt_or_ge n 3 with h3 | h3
      · obtain rfl : n = 2 := by omega
        simp (disch := omega) only [VG.Proof.Divstep.ite_t] at h
        simp (disch := omega) only [VG.Proof.Divstep.ite_f]
        refine VG.Proof.Divstep.inP_congr h ?_ ?_ <;> field_simp <;> ring
      · simp (disch := omega) only [VG.Proof.Divstep.ite_f] at h ⊢
        refine VG.Proof.Divstep.inP_congr h ?_ ?_ <;> simp only [pow_succ, mul_pow] <;> first | (field_simp; done) | (field_simp; ring)

/-- A step from `i = -j` to `i + 1` with `g` even. -/
theorem Wneg_even {j : Nat} {x y : ℚ} (h : VG.Proof.Divstep.Wneg j x y) :
    (j = 1 → VG.Proof.Divstep.Wpos 0 (x / VG.Proof.Divstep.s) (y / (2 * VG.Proof.Divstep.s))) ∧ (2 ≤ j → VG.Proof.Divstep.Wneg (j - 1) (x / VG.Proof.Divstep.s) (y / (2 * VG.Proof.Divstep.s))) := by
  have hs := VG.Proof.Divstep.s_ne
  unfold VG.Proof.Divstep.Wneg at h
  refine ⟨fun hj => ?_, fun hj => ?_⟩
  · subst hj
    simp only [↓reduceIte] at h
    unfold VG.Proof.Divstep.Wpos; simp (disch := omega) only [VG.Proof.Divstep.ite_t, pow_zero, mul_one]
    refine VG.Proof.Divstep.incl_at VG.Proof.Divstep.incl0_ok (x := x) (y := y) (by exact h) ?_ ?_ <;>
      simp only [VG.Proof.Divstep.incl0, LinMap.fx, LinMap.fy, LinMap.q] <;> push_cast <;> field_simp <;> ring
  · unfold VG.Proof.Divstep.Wneg
    rcases Nat.lt_or_ge j 3 with h3 | h3
    · obtain rfl : j = 2 := by omega
      simp (disch := omega) only [VG.Proof.Divstep.ite_f] at h ⊢
      refine VG.Proof.Divstep.incl_at VG.Proof.Divstep.inclN2_ok (x := (x - 2 * y) * VG.Proof.Divstep.s ^ 3) (y := 4 * x * VG.Proof.Divstep.s ^ 3) (by exact h) ?_ ?_ <;>
        simp only [VG.Proof.Divstep.inclN2, LinMap.fx, LinMap.fy, LinMap.q] <;> push_cast <;> field_simp <;> ring
    · simp (disch := omega) only [VG.Proof.Divstep.ite_f] at h
      rcases Nat.lt_or_ge j 4 with h4 | h4
      · obtain rfl : j = 3 := by omega
        simp (disch := omega) only [VG.Proof.Divstep.ite_f]
        refine VG.Proof.Divstep.incl_at VG.Proof.Divstep.inclN4scale_ok (x := VG.Proof.Divstep.c32 * (x - 2 * y) * VG.Proof.Divstep.s ^ (3 + 1))
          (y := VG.Proof.Divstep.c32 * x * VG.Proof.Divstep.s ^ (3 + 1) * 2 ^ 3) (by exact h) ?_ ?_ <;>
          simp only [VG.Proof.Divstep.inclN4scale, LinMap.fx, LinMap.fy, LinMap.q] <;> push_cast <;> field_simp <;> ring
      · simp (disch := omega) only [VG.Proof.Divstep.ite_f]
        obtain ⟨k, rfl⟩ : ∃ k, j = k + 4 := ⟨j - 4, by omega⟩
        refine VG.Proof.Divstep.inP_congr (VG.Proof.Divstep.H1_shear h (m := k + 3) (by omega)).1 ?_ ?_ <;>
          (simp only [show k + 4 - 1 = k + 3 from by omega, pow_succ]
           first | (field_simp; done) | (field_simp; ring))

/-- A step from `i = -j` to `i + 1` with `g` odd. -/
theorem Wneg_odd {j : Nat} {x y : ℚ} (h : VG.Proof.Divstep.Wneg j x y) :
    (j = 1 → VG.Proof.Divstep.Wpos 0 (x / VG.Proof.Divstep.s) ((y + x) / (2 * VG.Proof.Divstep.s))) ∧ (2 ≤ j → VG.Proof.Divstep.Wneg (j - 1) (x / VG.Proof.Divstep.s) ((y + x) / (2 * VG.Proof.Divstep.s))) := by
  have hs := VG.Proof.Divstep.s_ne
  unfold VG.Proof.Divstep.Wneg at h
  refine ⟨fun hj => ?_, fun hj => ?_⟩
  · subst hj
    simp only [↓reduceIte] at h
    unfold VG.Proof.Divstep.Wpos; simp (disch := omega) only [VG.Proof.Divstep.ite_t, pow_zero, mul_one]
    refine VG.Proof.Divstep.incl_at VG.Proof.Divstep.incl1_ok (x := x) (y := y) (by exact h) ?_ ?_ <;>
      simp only [VG.Proof.Divstep.incl1, LinMap.fx, LinMap.fy, LinMap.q] <;> push_cast <;> field_simp <;> ring
  · unfold VG.Proof.Divstep.Wneg
    rcases Nat.lt_or_ge j 3 with h3 | h3
    · obtain rfl : j = 2 := by omega
      simp (disch := omega) only [VG.Proof.Divstep.ite_f] at h ⊢
      refine VG.Proof.Divstep.incl_at VG.Proof.Divstep.inclN1_ok (x := (x - 2 * y) * VG.Proof.Divstep.s ^ 3) (y := 4 * x * VG.Proof.Divstep.s ^ 3) (by exact h) ?_ ?_ <;>
        simp only [VG.Proof.Divstep.inclN1, LinMap.fx, LinMap.fy, LinMap.q] <;> push_cast <;> field_simp <;> ring
    · simp (disch := omega) only [VG.Proof.Divstep.ite_f] at h
      rcases Nat.lt_or_ge j 4 with h4 | h4
      · obtain rfl : j = 3 := by omega
        simp (disch := omega) only [VG.Proof.Divstep.ite_f]
        refine VG.Proof.Divstep.incl_at VG.Proof.Divstep.inclN3scale_ok (x := VG.Proof.Divstep.c32 * (x - 2 * y) * VG.Proof.Divstep.s ^ (3 + 1))
          (y := VG.Proof.Divstep.c32 * x * VG.Proof.Divstep.s ^ (3 + 1) * 2 ^ 3) (by exact h) ?_ ?_ <;>
          simp only [VG.Proof.Divstep.inclN3scale, LinMap.fx, LinMap.fy, LinMap.q] <;> push_cast <;> field_simp <;> ring
      · simp (disch := omega) only [VG.Proof.Divstep.ite_f]
        obtain ⟨k, rfl⟩ : ∃ k, j = k + 4 := ⟨j - 4, by omega⟩
        refine VG.Proof.Divstep.inP_congr (VG.Proof.Divstep.H1_shear h (m := k + 3) (by omega)).2 ?_ ?_ <;>
          (simp only [show k + 4 - 1 = k + 3 from by omega, pow_succ]
           first | (field_simp; done) | (field_simp; ring))

end VG.Proof.Divstep

end

/- Proofs formerly in `VerifiedGarbage.Proof.Divstep.Bound`. -/
section

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

theorem W_pos {n : Nat} {x y : ℚ} : VG.Proof.Divstep.W n x y ↔ VG.Proof.Divstep.Wpos n x y := by
  unfold VG.Proof.Divstep.W; rw [VG.Proof.Divstep.ite_t (by omega)]; rfl

theorem W_neg {j : Nat} (hj : 1 ≤ j) {x y : ℚ} : VG.Proof.Divstep.W (-(j : Int)) x y ↔ VG.Proof.Divstep.Wneg j x y := by
  unfold VG.Proof.Divstep.W; rw [VG.Proof.Divstep.ite_f (by omega), show (-(-(j : Int))).toNat = j by omega]

/-- A step keeps the scaled point in `W`. -/
theorem W_step {i i' : Int} {x y : ℚ} {f g f' g' : ℚ} (c : ℚ) (hc : c ≠ 0) (hx : x = f / c) (hy : y = g / c)
    (h : VG.Proof.Divstep.W i x y) (hs : VG.Proof.Divstep.Step i f g i' f' g') : VG.Proof.Divstep.W i' (f' / (c * VG.Proof.Divstep.s)) (g' / (c * VG.Proof.Divstep.s)) := by
  have hs0 := VG.Proof.Divstep.s_ne
  subst hx hy
  rcases hs with ⟨rfl, hf', hg'⟩ | hs
  · -- The even step.
    rw [hf', hg']
    have e1 : f / (c * VG.Proof.Divstep.s) = f / c / VG.Proof.Divstep.s := by field_simp
    have e2 : g / 2 / (c * VG.Proof.Divstep.s) = g / c / (2 * VG.Proof.Divstep.s) := by fsr
    rw [e1, e2]
    rcases Int.lt_or_le i 0 with hi | hi
    · obtain ⟨j, rfl⟩ : ∃ j : Nat, i = -(j : Int) := ⟨(-i).toNat, by omega⟩
      have hj : 1 ≤ j := by omega
      have := VG.Proof.Divstep.Wneg_even ((VG.Proof.Divstep.W_neg hj).mp h)
      rcases Nat.lt_or_ge j 2 with h2 | h2
      · obtain rfl : j = 1 := by omega
        rw [show -((1 : Nat) : Int) + 1 = ((0 : Nat) : Int) by omega, VG.Proof.Divstep.W_pos]; exact this.1 rfl
      · rw [show -(j : Int) + 1 = -((j - 1 : Nat) : Int) by omega, VG.Proof.Divstep.W_neg (by omega)]; exact this.2 h2
    · obtain ⟨n, rfl⟩ : ∃ n : Nat, i = n := ⟨i.toNat, by omega⟩
      rw [show (n : Int) + 1 = ((n + 1 : Nat) : Int) by omega, VG.Proof.Divstep.W_pos]
      exact VG.Proof.Divstep.Wpos_even (W_pos.mp h)
  · split at hs
    · rename_i hi
      obtain ⟨rfl, hf', hg'⟩ := hs
      rw [hf', hg']
      have e1 : f / (c * VG.Proof.Divstep.s) = f / c / VG.Proof.Divstep.s := by field_simp
      have e2 : (g + f) / 2 / (c * VG.Proof.Divstep.s) = (g / c + f / c) / (2 * VG.Proof.Divstep.s) := by fsr
      rw [e1, e2]
      obtain ⟨j, rfl⟩ : ∃ j : Nat, i = -(j : Int) := ⟨(-i).toNat, by omega⟩
      have hj : 1 ≤ j := by omega
      have := VG.Proof.Divstep.Wneg_odd ((VG.Proof.Divstep.W_neg hj).mp h)
      rcases Nat.lt_or_ge j 2 with h2 | h2
      · obtain rfl : j = 1 := by omega
        rw [show -((1 : Nat) : Int) + 1 = ((0 : Nat) : Int) by omega, VG.Proof.Divstep.W_pos]; exact this.1 rfl
      · rw [show -(j : Int) + 1 = -((j - 1 : Nat) : Int) by omega, VG.Proof.Divstep.W_neg (by omega)]; exact this.2 h2
    · rename_i hi
      obtain ⟨rfl, hf', hg'⟩ := hs
      rw [hf', hg']
      have e1 : g / (c * VG.Proof.Divstep.s) = g / c / VG.Proof.Divstep.s := by field_simp
      have e2 : (g - f) / 2 / (c * VG.Proof.Divstep.s) = (g / c - f / c) / (2 * VG.Proof.Divstep.s) := by fsr
      rw [e1, e2]
      obtain ⟨n, rfl⟩ : ∃ n : Nat, i = n := ⟨i.toNat, by omega⟩
      have := VG.Proof.Divstep.Wpos_odd (W_pos.mp h)
      rcases Nat.lt_or_ge n 1 with h1 | h1
      · obtain rfl : n = 0 := by omega
        rw [show -((0 : Nat) : Int) = ((0 : Nat) : Int) by omega, VG.Proof.Divstep.W_pos]; exact this.1 rfl
      · rw [VG.Proof.Divstep.W_neg h1]; exact this.2 h1

/-- A run of the relaxed iteration from `i = 0`. -/
structure Run (i : Nat → Int) (f g : Nat → ℚ) : Prop where
  i0 : i 0 = 0
  step : ∀ n, VG.Proof.Divstep.Step (i n) (f n) (g n) (i (n + 1)) (f (n + 1)) (g (n + 1))

/-- The points of a run stay in the polygons `W`. -/
theorem stable {i : Nat → Int} {f g : Nat → ℚ} (hr : VG.Proof.Divstep.Run i f g) {u : ℚ} (hu : 0 < u)
    (h0 : VG.Proof.Divstep.H1P (f 0 / u) (g 0 / u)) : ∀ m, VG.Proof.Divstep.W (i m) (f m / (u * VG.Proof.Divstep.s ^ m)) (g m / (u * VG.Proof.Divstep.s ^ m))
  | 0 => by
    rw [hr.i0, show (0 : Int) = ((0 : Nat) : Int) from rfl, VG.Proof.Divstep.W_pos]
    unfold VG.Proof.Divstep.Wpos; rw [VG.Proof.Divstep.ite_t (by omega)]
    simpa using h0
  | m + 1 => by
    have := VG.Proof.Divstep.W_step (u * VG.Proof.Divstep.s ^ m) (by have := VG.Proof.Divstep.s_pos; positivity) rfl rfl (VG.Proof.Divstep.stable hr hu h0 m) (hr.step m)
    rwa [pow_succ, ← mul_assoc]

/-- The lattice scale `L`. -/
abbrev Lsc : ℚ := 3047 / 2048

instance (P : List VG.Proof.Divstep.Row) (x y : ℚ) : Decidable (VG.Proof.Divstep.inP P x y) := by unfold VG.Proof.Divstep.inP; infer_instance

/-- A point `(a, b) / u` of `H1` with `0 < u ≤ L` is `(a, b) / L` scaled. -/
theorem H1_atL {a b u : ℚ} (h : VG.Proof.Divstep.H1P (a / u) (b / u)) (hu : 0 < u) (huL : u ≤ VG.Proof.Divstep.Lsc) : VG.Proof.Divstep.H1P (a / VG.Proof.Divstep.Lsc) (b / VG.Proof.Divstep.Lsc) :=
  VG.Proof.Divstep.inP_congr (VG.Proof.Divstep.H1_shrink h (t := u / VG.Proof.Divstep.Lsc) (by positivity) (by rw [div_le_one (by norm_num)]; exact huL))
    (by field_simp) (by field_simp)

theorem s2_ge : (1 : ℚ) ≤ 2 * VG.Proof.Divstep.s ^ 2 := by unfold VG.Proof.Divstep.s VG.Proof.Divstep.sn VG.Proof.Divstep.sd; norm_num

/-- A nonzero integer `y` with `Wpos n (x / t) (y / t)` bounds `t s^n` below. -/
theorem lattice {n : Nat} {x y : Int} (hy : y ≠ 0) {t : ℚ} (ht : 0 < t) (h : VG.Proof.Divstep.Wpos n (x / t) (y / t)) :
    VG.Proof.Divstep.Lsc < t * VG.Proof.Divstep.s ^ n := by
  have hs := VG.Proof.Divstep.s_pos
  by_contra hc
  have hc := not_lt.mp hc
  have hu : 0 < t * VG.Proof.Divstep.s ^ n := by positivity
  have hy1 : (1 : ℚ) ≤ |(y : ℚ)| := by
    have : (1 : Int) ≤ |y| := Int.one_le_abs hy
    exact_mod_cast this
  unfold VG.Proof.Divstep.Wpos at h
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · rw [VG.Proof.Divstep.ite_t (by omega)] at h
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · rcases Nat.lt_or_ge n 1 with h1 | h1
      · obtain rfl : n = 0 := by omega
        have h' := VG.Proof.Divstep.H1_atL (a := x) (b := y) (u := t) (by simpa using h) ht (by simpa using hc)
        obtain ⟨bx, bY⟩ := VG.Proof.Divstep.H1_box h'
        rw [abs_le] at bx bY
        have hx : x = -1 ∨ x = 0 ∨ x = 1 := by
          have : (-2 : ℚ) < x ∧ (x : ℚ) < 2 := by constructor <;> nlinarith [bx.1, bx.2]
          have a : (-2 : Int) < x := by exact_mod_cast this.1
          have b : x < (2 : Int) := by exact_mod_cast this.2
          omega
        have hyv : y = -1 ∨ y = 1 := by
          have : (-2 : ℚ) < y ∧ (y : ℚ) < 2 := by constructor <;> nlinarith [bY.1, bY.2]
          have a : (-2 : Int) < y := by exact_mod_cast this.1
          have b : y < (2 : Int) := by exact_mod_cast this.2
          omega
        rcases hx with rfl | rfl | rfl <;> rcases hyv with rfl | rfl <;> revert h' <;> decide +kernel
      · obtain rfl : n = 1 := by omega
        have h' := VG.Proof.Divstep.H1_atL (a := x * VG.Proof.Divstep.s ^ 2) (b := 2 * y * VG.Proof.Divstep.s ^ 2) (u := t * VG.Proof.Divstep.s ^ 1)
          (VG.Proof.Divstep.inP_congr h (by field_simp) (by fsr)) hu hc
        obtain ⟨bx, bY⟩ := VG.Proof.Divstep.H1_box h'
        rw [abs_le] at bx bY
        have hs2 : VG.Proof.Divstep.s ^ 2 = 954973097164321 / 1743039955072900 := by unfold VG.Proof.Divstep.s VG.Proof.Divstep.sn VG.Proof.Divstep.sd; norm_num
        rw [hs2] at bx bY
        have hx : x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 := by
          have : (-3 : ℚ) < x ∧ (x : ℚ) < 3 := by constructor <;> nlinarith [bx.1, bx.2]
          have a : (-3 : Int) < x := by exact_mod_cast this.1
          have b : x < (3 : Int) := by exact_mod_cast this.2
          omega
        have hyv : y = -1 ∨ y = 1 := by
          have : (-2 : ℚ) < y ∧ (y : ℚ) < 2 := by constructor <;> nlinarith [bY.1, bY.2]
          have a : (-2 : Int) < y := by exact_mod_cast this.1
          have b : y < (2 : Int) := by exact_mod_cast this.2
          omega
        rw [hs2] at h'
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> rcases hyv with rfl | rfl <;> revert h' <;> decide +kernel
    · obtain rfl : n = 2 := by omega
      have h' := VG.Proof.Divstep.H1_atL (a := x * VG.Proof.Divstep.s ^ 4) (b := 4 * y * VG.Proof.Divstep.s ^ 4) (u := t * VG.Proof.Divstep.s ^ 2)
        (VG.Proof.Divstep.inP_congr h (by fsr) (by fsr)) hu hc
      have bY := (VG.Proof.Divstep.H1_box h').2
      have hs4 : (379 / 512 : ℚ) * VG.Proof.Divstep.Lsc / (4 * VG.Proof.Divstep.s ^ 4) < 1 := by unfold VG.Proof.Divstep.s VG.Proof.Divstep.sn VG.Proof.Divstep.sd; norm_num
      have : |(y : ℚ)| * (4 * VG.Proof.Divstep.s ^ 4) / VG.Proof.Divstep.Lsc ≤ 379 / 512 := by
        rw [abs_div, abs_mul, abs_mul, abs_of_pos (show (0 : ℚ) < VG.Proof.Divstep.Lsc by norm_num),
          abs_of_pos (show (0 : ℚ) < 4 by norm_num), abs_of_pos (by positivity : (0 : ℚ) < s ^ 4)] at bY
        linarith [bY]
      have : |(y : ℚ)| < 1 := by
        rw [div_le_iff₀ (by norm_num)] at this
        rw [div_lt_one (by positivity)] at hs4
        nlinarith
      linarith
  · rw [VG.Proof.Divstep.ite_f (by omega)] at h
    have h' := VG.Proof.Divstep.H1_atL (a := VG.Proof.Divstep.c32 * x * VG.Proof.Divstep.s ^ (2 * n)) (b := VG.Proof.Divstep.c32 * y * 2 ^ n * VG.Proof.Divstep.s ^ (2 * n)) (u := t * VG.Proof.Divstep.s ^ n)
      (VG.Proof.Divstep.inP_congr h (by rw [pow_mul']; fsr) (by rw [pow_mul', mul_pow]; fsr)) hu hc
    have bY := (VG.Proof.Divstep.H1_box h').2
    have hp : (2 * VG.Proof.Divstep.s ^ 2) ^ 3 ≤ (2 * VG.Proof.Divstep.s ^ 2) ^ n := pow_le_pow_right₀ VG.Proof.Divstep.s2_ge h3
    have hb : (379 / 512 : ℚ) * (33 / 32) * VG.Proof.Divstep.Lsc / (2 * VG.Proof.Divstep.s ^ 2) ^ 3 < 1 := by unfold VG.Proof.Divstep.s VG.Proof.Divstep.sn VG.Proof.Divstep.sd; norm_num
    have e : VG.Proof.Divstep.c32 * y * 2 ^ n * VG.Proof.Divstep.s ^ (2 * n) = VG.Proof.Divstep.c32 * y * (2 * VG.Proof.Divstep.s ^ 2) ^ n := by rw [mul_pow, pow_mul]; ring
    rw [e] at bY
    have hp0 : (0 : ℚ) < (2 * VG.Proof.Divstep.s ^ 2) ^ 3 := by positivity
    have hpn : (0 : ℚ) < (2 * VG.Proof.Divstep.s ^ 2) ^ n := by positivity
    have : |(y : ℚ)| * (2 * VG.Proof.Divstep.s ^ 2) ^ n ≤ (379 / 512) * (33 / 32) * VG.Proof.Divstep.Lsc := by
      rw [abs_div, abs_mul, abs_mul, abs_of_pos (show (0 : ℚ) < VG.Proof.Divstep.Lsc by norm_num),
        abs_of_pos (show (0 : ℚ) < VG.Proof.Divstep.c32 by norm_num), abs_of_pos hpn, div_le_iff₀ (by norm_num)] at bY
      unfold VG.Proof.Divstep.c32 at bY
      nlinarith [abs_nonneg (y : ℚ)]
    rw [div_lt_one hp0] at hb
    nlinarith [abs_nonneg (y : ℚ)]

/-- `j(i)`: `i` for `i ≥ 0`, `-i - 1` else. -/
def J (i : Int) : Nat := if 0 ≤ i then i.toNat else (-i).toNat - 1

/-- A run whose `g` stays nonzero until `m` has `L < u s^(m + J (i m))`. -/
theorem sizeBound {i : Nat → Int} {f g : Nat → ℚ} (hr : VG.Proof.Divstep.Run i f g) {u : ℚ} (hu : 0 < u)
    (h0 : VG.Proof.Divstep.H1P (f 0 / u) (g 0 / u)) (hf : ∀ n, ∃ z : Int, f n = z) (hg : ∀ n, ∃ z : Int, g n = z) :
    ∀ m, (∀ n ≤ m, g n ≠ 0) → VG.Proof.Divstep.Lsc < u * VG.Proof.Divstep.s ^ (m + VG.Proof.Divstep.J (i m)) := by
  have hs := VG.Proof.Divstep.s_pos
  intro m
  induction m with
  | zero => ?_
  | succ m ih => ?_
  all_goals intro hnz
  · -- `i 0 = 0`.
    obtain ⟨x, hx⟩ := hf 0
    obtain ⟨y, hy⟩ := hg 0
    have h := VG.Proof.Divstep.stable hr hu h0 0
    rw [hr.i0, show (0 : Int) = ((0 : Nat) : Int) from rfl, VG.Proof.Divstep.W_pos] at h
    rw [hx, hy] at h
    have := VG.Proof.Divstep.lattice (n := 0) (x := x) (y := y) (by intro e; exact hnz 0 (Nat.le_refl _) (by rw [hy, e]; simp))
      (t := u * VG.Proof.Divstep.s ^ 0) (by positivity) h
    simpa [hr.i0, VG.Proof.Divstep.J] using this
  · rcases Int.lt_or_le (i (m + 1)) 0 with hi | hi
    · have ih' := ih fun n hn => hnz n (by omega)
      have e : m + VG.Proof.Divstep.J (i m) = m + 1 + VG.Proof.Divstep.J (i (m + 1)) := by
        have st := hr.step m
        unfold VG.Proof.Divstep.J
        rcases st with ⟨h1, -, -⟩ | st
        · rw [VG.Proof.Divstep.ite_f (by omega), VG.Proof.Divstep.ite_f (by omega)]; omega
        · split at st
          · rw [VG.Proof.Divstep.ite_f (by omega), VG.Proof.Divstep.ite_f (by omega)]; omega
          · obtain ⟨h1, -, -⟩ := st
            rw [VG.Proof.Divstep.ite_t (by omega), VG.Proof.Divstep.ite_f (by omega)]; omega
      rw [← e]; exact ih'
    · obtain ⟨x, hx⟩ := hf (m + 1)
      obtain ⟨y, hy⟩ := hg (m + 1)
      have h := VG.Proof.Divstep.stable hr hu h0 (m + 1)
      obtain ⟨n, hn⟩ : ∃ n : Nat, i (m + 1) = n := ⟨(i (m + 1)).toNat, by omega⟩
      rw [hn, VG.Proof.Divstep.W_pos, hx, hy] at h
      have := VG.Proof.Divstep.lattice (x := x) (y := y) (by intro e; exact hnz (m + 1) (Nat.le_refl _) (by rw [hy, e]; simp))
        (by positivity) h
      rw [hn, show VG.Proof.Divstep.J (n : Int) = n by simp [VG.Proof.Divstep.J], pow_add, ← mul_assoc]
      exact this

/-- The fuzziness `2753/4096 · L`. -/
abbrev fuzz : ℚ := 8388391 / 8388608

/-- A run of integers from `0 ≤ g 0 ≤ f 0 ≤ M` reaches `g = 0` by step `m`
when `M s^m ≤ 2753/4096 · L`. -/
theorem endToEnd {i : Nat → Int} {f g : Nat → ℚ} (hr : VG.Proof.Divstep.Run i f g) (hf : ∀ n, ∃ z : Int, f n = z)
    (hg : ∀ n, ∃ z : Int, g n = z) {M : ℚ} (hg0 : 0 ≤ g 0) (hgf : g 0 ≤ f 0) (hfM : f 0 ≤ M) {m : Nat}
    (hm : M * VG.Proof.Divstep.s ^ m ≤ VG.Proof.Divstep.fuzz) : ∃ n ≤ m, g n = 0 := by
  have hs := VG.Proof.Divstep.s_pos
  have hs1 := VG.Proof.Divstep.s_lt_one
  by_contra hc
  have hc : ∀ n ≤ m, g n ≠ 0 := fun n hn e => hc ⟨n, hn, e⟩
  rcases lt_or_eq_of_le (le_trans hg0 (le_trans hgf hfM)) with hM | hM
  · set u := M * (4096 / 2753) with hu
    have hu0 : 0 < u := by positivity
    have q1 : f 0 / M ≤ 1 := (div_le_one hM).mpr hfM
    have q2 : g 0 / M ≤ f 0 / M := div_le_div_of_nonneg_right hgf hM.le
    have q3 : 0 ≤ g 0 / M := div_nonneg hg0 hM.le
    have hin : VG.Proof.Divstep.inP VG.Proof.Divstep.Hinit (f 0 / M) (g 0 / M) := by
      intro r hr
      simp only [VG.Proof.Divstep.Hinit, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> push_cast <;> linarith
    have h0 : VG.Proof.Divstep.H1P (f 0 / u) (g 0 / u) :=
      VG.Proof.Divstep.incl_at VG.Proof.Divstep.inclInit_ok hin (by simp only [VG.Proof.Divstep.inclInit, LinMap.fx, LinMap.q]; push_cast; field_simp; ring)
        (by simp only [VG.Proof.Divstep.inclInit, LinMap.fy, LinMap.q]; push_cast; field_simp; ring)
    have hb := VG.Proof.Divstep.sizeBound hr hu0 h0 hf hg m hc
    have hle : u * VG.Proof.Divstep.s ^ (m + VG.Proof.Divstep.J (i m)) ≤ u * VG.Proof.Divstep.s ^ m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs.le hs1.le (Nat.le_add_right _ _)) hu0.le
    have : u * VG.Proof.Divstep.s ^ m ≤ VG.Proof.Divstep.Lsc := by
      rw [hu, mul_assoc, mul_comm (4096 / 2753 : ℚ), ← mul_assoc]
      have := mul_le_mul_of_nonneg_right hm (show (0 : ℚ) ≤ 4096 / 2753 by norm_num)
      unfold VG.Proof.Divstep.fuzz at this; norm_num at this ⊢; linarith
    linarith
  · exact hc 0 (Nat.zero_le _) (le_antisymm (by rw [hM]; linarith) hg0)

end VG.Proof.Divstep

end

/- Proofs formerly in `VerifiedGarbage.Proof.Divstep.Iter`. -/
section

/-!
# The divstep and its bound

Bernstein–Yang's divstep in its "half-delta" form, as J. Harrison's
`idivstep` (HOL Light `Divstep/idivstep.ml`) and libsecp256k1's `divsteps`
iterate it: from `(d, f, g)` with `f` odd,
`(2 - d, g, (g - f)/2)` if `d ≥ 0` and `g` is odd, else
`(2 + d, f, (g + (g mod 2) f)/2)`, from `d = 1`. Its runs are runs of the
relaxed iteration for `i = (d - 1)/2` (`run`), so from `0 ≤ g ≤ f ≤ 2^256`,
`f` odd, `g` is zero after 590 steps (`g_590`), and `f` is then `± gcd(f, g)`
(`f_gcd`).
-/

namespace VG.Proof.Divstep

/-- One divstep on `(d, f, g)`. -/
def divstep (t : Int × Int × Int) : Int × Int × Int :=
  if 0 ≤ t.1 ∧ t.2.2 % 2 = 1 then (2 - t.1, t.2.2, (t.2.2 - t.2.1) / 2)
  else (2 + t.1, t.2.1, (t.2.2 + t.2.2 % 2 * t.2.1) / 2)

/-- `n` divsteps. -/
def divsteps : Nat → Int × Int × Int → Int × Int × Int
  | 0, t => t
  | n + 1, t => VG.Proof.Divstep.divsteps n (VG.Proof.Divstep.divstep t)

theorem divsteps_succ (n : Nat) (t : Int × Int × Int) : VG.Proof.Divstep.divsteps (n + 1) t = VG.Proof.Divstep.divstep (VG.Proof.Divstep.divsteps n t) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => rw [VG.Proof.Divstep.divsteps, ih, VG.Proof.Divstep.divsteps]

/-- The state after `n` steps: `d` odd, `f` odd. -/
theorem divsteps_odd {d f g : Int} (hd : d % 2 = 1) (hf : f % 2 = 1) :
    ∀ n, (VG.Proof.Divstep.divsteps n (d, f, g)).1 % 2 = 1 ∧ (VG.Proof.Divstep.divsteps n (d, f, g)).2.1 % 2 = 1
  | 0 => ⟨hd, hf⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := VG.Proof.Divstep.divsteps_odd hd hf n
    rw [VG.Proof.Divstep.divsteps_succ]
    generalize VG.Proof.Divstep.divsteps n (d, f, g) = t at h1 h2
    obtain ⟨d', f', g'⟩ := t
    simp only at h1 h2
    unfold VG.Proof.Divstep.divstep
    split
    · rename_i h; exact ⟨by omega, h.2⟩
    · exact ⟨by omega, h2⟩

/-- A zero `g` stays zero. -/
theorem divsteps_zero {t : Int × Int × Int} (h : t.2.2 = 0) : ∀ n, (VG.Proof.Divstep.divsteps n t).2.2 = 0 ∧ (VG.Proof.Divstep.divsteps n t).2.1 = t.2.1
  | 0 => ⟨h, rfl⟩
  | n + 1 => by
    obtain ⟨h1, h2⟩ := VG.Proof.Divstep.divsteps_zero h n
    rw [VG.Proof.Divstep.divsteps_succ]
    generalize VG.Proof.Divstep.divsteps n t = u at h1 h2
    obtain ⟨d', f', g'⟩ := u
    simp only at h1 h2
    subst h1
    unfold VG.Proof.Divstep.divstep
    simp [h2]

theorem divsteps_add (n k : Nat) (t : Int × Int × Int) : VG.Proof.Divstep.divsteps (n + k) t = VG.Proof.Divstep.divsteps k (VG.Proof.Divstep.divsteps n t) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← Nat.add_assoc, VG.Proof.Divstep.divsteps_succ, VG.Proof.Divstep.divsteps_succ, ih]

theorem ediv2_cast {a : Int} (h : a % 2 = 0) : ((a / 2 : Int) : ℚ) = (a : ℚ) / 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, a = 2 * k := ⟨a / 2, by omega⟩
  rw [Int.mul_ediv_cancel_left _ (by decide)]; push_cast; ring

/-- The divstep's runs are runs of the relaxed iteration, with `i = (d - 1)/2`. -/
theorem run {f g : Int} (hf : f % 2 = 1) :
    VG.Proof.Divstep.Run (fun n => ((VG.Proof.Divstep.divsteps n (1, f, g)).1 - 1) / 2) (fun n => ((VG.Proof.Divstep.divsteps n (1, f, g)).2.1 : ℚ))
      (fun n => ((VG.Proof.Divstep.divsteps n (1, f, g)).2.2 : ℚ)) := by
  refine ⟨by simp [VG.Proof.Divstep.divsteps], fun n => ?_⟩
  obtain ⟨hd, hf'⟩ := VG.Proof.Divstep.divsteps_odd (d := 1) (g := g) (by decide) hf n
  simp only [VG.Proof.Divstep.divsteps_succ]
  generalize VG.Proof.Divstep.divsteps n (1, f, g) = t at hd hf'
  obtain ⟨d, f', g'⟩ := t
  simp only at hd hf' ⊢
  unfold VG.Proof.Divstep.divstep VG.Proof.Divstep.Step
  simp only
  split
  · rename_i h
    obtain ⟨hd0, hg⟩ := h
    right
    rw [VG.Proof.Divstep.ite_f (by omega)]
    refine ⟨by omega, rfl, ?_⟩
    simp only; rw [VG.Proof.Divstep.ediv2_cast (a := g' - f') (by omega)]; push_cast; ring
  · rename_i h
    rcases Int.emod_two_eq_zero_or_one g' with hg | hg
    · left
      refine ⟨by omega, rfl, ?_⟩
      simp only [hg, zero_mul, add_zero]; exact VG.Proof.Divstep.ediv2_cast hg
    · right
      rw [VG.Proof.Divstep.ite_t (by omega)]
      refine ⟨by omega, rfl, ?_⟩
      simp only [hg, one_mul]; rw [VG.Proof.Divstep.ediv2_cast (by omega)]; push_cast; ring

/-- `2^b s^m` is at most the fuzziness, in naturals. -/
theorem pow_fuzz {b m : Nat} (h : 2 ^ b * VG.Proof.Divstep.sn ^ m * 8388608 ≤ 8388391 * VG.Proof.Divstep.sd ^ m) : (2 : ℚ) ^ b * VG.Proof.Divstep.s ^ m ≤ VG.Proof.Divstep.fuzz := by
  have hq : ((2 ^ b * VG.Proof.Divstep.sn ^ m * 8388608 : Nat) : ℚ) ≤ ((8388391 * VG.Proof.Divstep.sd ^ m : Nat) : ℚ) := by exact_mod_cast h
  push_cast at hq
  rw [VG.Proof.Divstep.s_pow, VG.Proof.Divstep.fuzz, mul_div_assoc', div_le_div_iff₀ (by unfold VG.Proof.Divstep.sd; positivity) (by norm_num)]
  linarith

/-- From `0 ≤ g ≤ f ≤ 2^b`, `f` odd, `g` is zero after any `n ≥ m` divsteps if
`2^b s^m` is at most the fuzziness. -/
theorem g_bound {f g : Int} (hf : f % 2 = 1) (hg : 0 ≤ g) (hgf : g ≤ f) {b m : Nat} (hf2 : f ≤ 2 ^ b)
    (hbm : (2 : ℚ) ^ b * VG.Proof.Divstep.s ^ m ≤ VG.Proof.Divstep.fuzz) {n : Nat} (hn : m ≤ n) : (VG.Proof.Divstep.divsteps n (1, f, g)).2.2 = 0 := by
  obtain ⟨k, hk, h0⟩ := VG.Proof.Divstep.endToEnd (VG.Proof.Divstep.run (g := g) hf) (fun n => ⟨_, rfl⟩) (fun n => ⟨_, rfl⟩)
    (M := 2 ^ b) (m := m) (by simp [VG.Proof.Divstep.divsteps]; exact_mod_cast hg)
    (by simp [VG.Proof.Divstep.divsteps]; exact_mod_cast hgf) (by simp [VG.Proof.Divstep.divsteps]; exact_mod_cast hf2) hbm
  simp only [Int.cast_eq_zero] at h0
  obtain ⟨j, rfl⟩ : ∃ j, n = k + j := ⟨n - k, by omega⟩
  rw [VG.Proof.Divstep.divsteps_add]
  exact (VG.Proof.Divstep.divsteps_zero h0 j).1

theorem gcd_two {a : Int} (ha : a % 2 = 1) : Int.gcd a 2 = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, a = 1 + k * 2 := ⟨a / 2, by omega⟩
  rw [Int.gcd_add_mul_right_left]; decide

/-- Halving with an odd other side keeps the gcd. -/
theorem gcd_half {a b : Int} (ha : a % 2 = 1) (hb : b % 2 = 0) : Int.gcd a (b / 2) = Int.gcd a b := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c * 2 := ⟨b / 2, by omega⟩
  rw [Int.mul_ediv_cancel _ (by decide), Int.gcd_mul_left_right_of_gcd_eq_one (VG.Proof.Divstep.gcd_two ha)]

/-- A divstep keeps `gcd(f, g)` (with `f` odd). -/
theorem divstep_gcd {d f g : Int} (hf : f % 2 = 1) :
    Int.gcd (VG.Proof.Divstep.divstep (d, f, g)).2.1 (VG.Proof.Divstep.divstep (d, f, g)).2.2 = Int.gcd f g := by
  unfold VG.Proof.Divstep.divstep
  simp only
  split
  · rename_i h
    rw [VG.Proof.Divstep.gcd_half h.2 (by omega), Int.gcd_self_sub_right, Int.gcd_comm]
  · rcases Int.emod_two_eq_zero_or_one g with hg | hg
    · rw [hg, zero_mul, add_zero, VG.Proof.Divstep.gcd_half hf hg]
    · rw [hg, one_mul, VG.Proof.Divstep.gcd_half hf (by omega)]
      have : g + f = g + 1 * f := by ring
      rw [this, Int.gcd_add_mul_right_right]

theorem divsteps_gcd {d f g : Int} (hd : d % 2 = 1) (hf : f % 2 = 1) :
    ∀ n, Int.gcd (VG.Proof.Divstep.divsteps n (d, f, g)).2.1 (VG.Proof.Divstep.divsteps n (d, f, g)).2.2 = Int.gcd f g
  | 0 => rfl
  | n + 1 => by
    rw [VG.Proof.Divstep.divsteps_succ]
    have hodd := (VG.Proof.Divstep.divsteps_odd (g := g) hd hf n).2
    have ih := VG.Proof.Divstep.divsteps_gcd (g := g) hd hf n
    generalize VG.Proof.Divstep.divsteps n (d, f, g) = t at hodd ih
    obtain ⟨d', f', g'⟩ := t
    rw [VG.Proof.Divstep.divstep_gcd hodd]; exact ih

/-- From `0 ≤ g ≤ f ≤ 2^b`, `f` odd, after any `n ≥ m` divsteps `g` is zero
and `|f| = gcd(f, g)`, if `2^b s^m` is at most the fuzziness. -/
theorem divsteps_bound {f g : Int} (hf : f % 2 = 1) (hg : 0 ≤ g) (hgf : g ≤ f) {b m : Nat} (hf2 : f ≤ 2 ^ b)
    (hbm : (2 : ℚ) ^ b * VG.Proof.Divstep.s ^ m ≤ VG.Proof.Divstep.fuzz) {n : Nat} (hn : m ≤ n) :
    (VG.Proof.Divstep.divsteps n (1, f, g)).2.2 = 0 ∧ (VG.Proof.Divstep.divsteps n (1, f, g)).2.1.natAbs = Int.gcd f g := by
  have h0 := VG.Proof.Divstep.g_bound hf hg hgf hf2 hbm hn
  refine ⟨h0, ?_⟩
  have := VG.Proof.Divstep.divsteps_gcd (d := 1) (g := g) (by decide) hf n
  rw [h0, Int.gcd_zero_right] at this
  exact this

/-- 256-bit moduli: 590 divsteps (`9437 b + 1 ≤ 4096 m`). -/
theorem divsteps_590 {f g : Int} (hf : f % 2 = 1) (hg : 0 ≤ g) (hgf : g ≤ f) (hf2 : f ≤ 2 ^ 256) {n : Nat}
    (hn : 590 ≤ n) : (VG.Proof.Divstep.divsteps n (1, f, g)).2.2 = 0 ∧ (VG.Proof.Divstep.divsteps n (1, f, g)).2.1.natAbs = Int.gcd f g :=
  VG.Proof.Divstep.divsteps_bound hf hg hgf hf2 (VG.Proof.Divstep.pow_fuzz (by decide +kernel)) hn

/-- 384-bit moduli: 885 divsteps. -/
theorem divsteps_885 {f g : Int} (hf : f % 2 = 1) (hg : 0 ≤ g) (hgf : g ≤ f) (hf2 : f ≤ 2 ^ 384) {n : Nat}
    (hn : 885 ≤ n) : (VG.Proof.Divstep.divsteps n (1, f, g)).2.2 = 0 ∧ (VG.Proof.Divstep.divsteps n (1, f, g)).2.1.natAbs = Int.gcd f g :=
  VG.Proof.Divstep.divsteps_bound hf hg hgf hf2 (VG.Proof.Divstep.pow_fuzz (by decide +kernel)) hn

end VG.Proof.Divstep

end

/- Proofs formerly in `VerifiedGarbage.Proof.Divstep.Batch`. -/
section

/-!
# Divsteps in batches

The divstep with its transition matrix (`mstep`, as J. Harrison's
`divstep_mat`): from the identity, `n` steps give `(d, f, g)` of `divsteps`
(`msteps_dfg`) and `(u, v, q, r)` with `2^n f_n = u f + v g`,
`2^n g_n = q f + r g` (`msteps_mat`), entries at most `2^n` (`msteps_bound`).
They read only `d` and `g mod 2`, so `n` steps on `f`, `g` taken modulo
`2^N` (`n ≤ N`) give the same `d` and matrix (`msteps_cong`): a batch runs on
the low words and its matrix updates the whole numbers.
-/

namespace VG.Proof.Divstep

/-- A divstep state and its transition matrix. -/
structure MSt where
  d : Int
  f : Int
  g : Int
  u : Int
  v : Int
  q : Int
  r : Int

/-- A divstep, with the matrix doubled and combined as `(f, g)` are. -/
def mstep (t : VG.Proof.Divstep.MSt) : VG.Proof.Divstep.MSt :=
  if 0 ≤ t.d ∧ t.g % 2 = 1 then ⟨2 - t.d, t.g, (t.g - t.f) / 2, 2 * t.q, 2 * t.r, t.q - t.u, t.r - t.v⟩
  else ⟨2 + t.d, t.f, (t.g + t.g % 2 * t.f) / 2, 2 * t.u, 2 * t.v, t.q + t.g % 2 * t.u, t.r + t.g % 2 * t.v⟩

/-- `n` such steps. -/
def msteps : Nat → VG.Proof.Divstep.MSt → VG.Proof.Divstep.MSt
  | 0, t => t
  | n + 1, t => VG.Proof.Divstep.msteps n (VG.Proof.Divstep.mstep t)

/-- The start of a batch: `(d, f, g)` and the identity. -/
def MSt.init (d f g : Int) : VG.Proof.Divstep.MSt := ⟨d, f, g, 1, 0, 0, 1⟩

theorem msteps_succ (n : Nat) (t : VG.Proof.Divstep.MSt) : VG.Proof.Divstep.msteps (n + 1) t = VG.Proof.Divstep.mstep (VG.Proof.Divstep.msteps n t) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => rw [VG.Proof.Divstep.msteps, ih, VG.Proof.Divstep.msteps]

/-- The state is `divsteps`'. -/
theorem msteps_dfg (n : Nat) (t : VG.Proof.Divstep.MSt) :
    ((VG.Proof.Divstep.msteps n t).d, (VG.Proof.Divstep.msteps n t).f, (VG.Proof.Divstep.msteps n t).g) = VG.Proof.Divstep.divsteps n (t.d, t.f, t.g) := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [VG.Proof.Divstep.msteps, ih, VG.Proof.Divstep.divsteps]
    congr 1
    unfold VG.Proof.Divstep.mstep VG.Proof.Divstep.divstep
    split <;> rfl

/-- The matrix: `2^k f = u f₀ + v g₀`, `2^k g = q f₀ + r g₀` is kept, with `k + 1`,
by a step from an odd `f`. -/
def MSt.rel (t : VG.Proof.Divstep.MSt) (k : Nat) (f₀ g₀ : Int) : Prop :=
  2 ^ k * t.f = t.u * f₀ + t.v * g₀ ∧ 2 ^ k * t.g = t.q * f₀ + t.r * g₀

theorem mstep_rel {t : VG.Proof.Divstep.MSt} {k : Nat} {f₀ g₀ : Int} (hf : t.f % 2 = 1) (h : t.rel k f₀ g₀) :
    (VG.Proof.Divstep.mstep t).rel (k + 1) f₀ g₀ := by
  obtain ⟨h1, h2⟩ := h
  unfold VG.Proof.Divstep.mstep MSt.rel
  split
  · rename_i hc
    simp only
    have e : 2 * ((t.g - t.f) / 2) = t.g - t.f := Int.mul_ediv_cancel' (by omega)
    constructor
    · rw [pow_succ]; linear_combination 2 * h2
    · rw [pow_succ, mul_assoc, e]; linear_combination h2 - h1
  · rename_i hc
    simp only
    rcases Int.emod_two_eq_zero_or_one t.g with hg | hg
    · rw [hg]
      have e : 2 * ((t.g + 0 * t.f) / 2) = t.g := by rw [zero_mul, add_zero]; exact Int.mul_ediv_cancel' (by omega)
      constructor
      · rw [pow_succ]; linear_combination 2 * h1
      · rw [pow_succ, mul_assoc, e]; linear_combination h2
    · rw [hg]
      have e : 2 * ((t.g + 1 * t.f) / 2) = t.g + t.f := by rw [one_mul]; exact Int.mul_ediv_cancel' (by omega)
      constructor
      · rw [pow_succ]; linear_combination 2 * h1
      · rw [pow_succ, mul_assoc, e]; linear_combination h2 + h1

/-- `f` stays odd. -/
theorem mstep_f_odd {t : VG.Proof.Divstep.MSt} (hf : t.f % 2 = 1) : (VG.Proof.Divstep.mstep t).f % 2 = 1 := by
  unfold VG.Proof.Divstep.mstep; split
  · rename_i h; exact h.2
  · exact hf

theorem msteps_f_odd {t : VG.Proof.Divstep.MSt} (hf : t.f % 2 = 1) : ∀ n, (VG.Proof.Divstep.msteps n t).f % 2 = 1
  | 0 => hf
  | n + 1 => by rw [VG.Proof.Divstep.msteps_succ]; exact VG.Proof.Divstep.mstep_f_odd (VG.Proof.Divstep.msteps_f_odd hf n)

/-- `n` steps from the identity: `2^n f_n = u f + v g`, `2^n g_n = q f + r g`. -/
theorem msteps_mat {d f g : Int} (hf : f % 2 = 1) (n : Nat) :
    (VG.Proof.Divstep.msteps n (MSt.init d f g)).rel n f g := by
  induction n with
  | zero => simp [MSt.rel, MSt.init, VG.Proof.Divstep.msteps]
  | succ n ih =>
    rw [VG.Proof.Divstep.msteps_succ]
    exact VG.Proof.Divstep.mstep_rel (VG.Proof.Divstep.msteps_f_odd (t := MSt.init d f g) hf n) ih

/-- The matrix's rows have `|u| + |v| ≤ 2^n` and `|q| + |r| ≤ 2^n` after `n` steps
from the identity. -/
def MSt.bnd (t : VG.Proof.Divstep.MSt) (n : Nat) : Prop := |t.u| + |t.v| ≤ 2 ^ n ∧ |t.q| + |t.r| ≤ 2 ^ n

theorem mstep_bnd {t : VG.Proof.Divstep.MSt} {n : Nat} (h : t.bnd n) : (VG.Proof.Divstep.mstep t).bnd (n + 1) := by
  obtain ⟨h1, h2⟩ := h
  have hb : ∀ b : Int, (b = 0 ∨ b = 1) → ∀ x : Int, |b * x| ≤ |x| := fun b hb x => by
    rcases hb with rfl | rfl <;> simp
  have hg := Int.emod_two_eq_zero_or_one t.g
  unfold VG.Proof.Divstep.mstep MSt.bnd
  rw [pow_succ]
  split
  · simp only
    refine ⟨?_, ?_⟩
    · rw [abs_mul, abs_mul]; norm_num; linarith
    · have := abs_sub t.q t.u; have := abs_sub t.r t.v; linarith
  · simp only
    refine ⟨?_, ?_⟩
    · rw [abs_mul, abs_mul]; norm_num; linarith
    · have := abs_add_le t.q (t.g % 2 * t.u); have := abs_add_le t.r (t.g % 2 * t.v)
      have := hb _ hg t.u; have := hb _ hg t.v; linarith

theorem msteps_bnd (d f g : Int) : ∀ n, (VG.Proof.Divstep.msteps n (MSt.init d f g)).bnd n
  | 0 => by simp [MSt.bnd, MSt.init, VG.Proof.Divstep.msteps]
  | n + 1 => by rw [VG.Proof.Divstep.msteps_succ]; exact VG.Proof.Divstep.mstep_bnd (VG.Proof.Divstep.msteps_bnd d f g n)

/-- `|d|` grows by at most 2 a step. -/
theorem mstep_d (t : VG.Proof.Divstep.MSt) : |(VG.Proof.Divstep.mstep t).d| ≤ |t.d| + 2 := by
  unfold VG.Proof.Divstep.mstep; split <;> simp only <;> rw [abs_le] <;> constructor <;>
    linarith [abs_nonneg t.d, le_abs_self t.d, neg_abs_le t.d]

theorem msteps_d (t : VG.Proof.Divstep.MSt) : ∀ n, |(VG.Proof.Divstep.msteps n t).d| ≤ |t.d| + 2 * n
  | 0 => by simp [VG.Proof.Divstep.msteps]
  | n + 1 => by
    rw [VG.Proof.Divstep.msteps_succ]
    have := VG.Proof.Divstep.mstep_d (VG.Proof.Divstep.msteps n t)
    have := VG.Proof.Divstep.msteps_d t n
    push_cast; linarith

/-- States with the same `d` and matrix, and `f`, `g` congruent modulo `2^k`. -/
def MSt.cong (t t' : VG.Proof.Divstep.MSt) (k : Nat) : Prop :=
  t.d = t'.d ∧ t.u = t'.u ∧ t.v = t'.v ∧ t.q = t'.q ∧ t.r = t'.r ∧
    t.f % 2 ^ k = t'.f % 2 ^ k ∧ t.g % 2 ^ k = t'.g % 2 ^ k

/-- Halving congruent even numbers. -/
theorem half_cong {a a' : Int} {k : Nat} (h : a % 2 ^ (k + 1) = a' % 2 ^ (k + 1)) (ha : a % 2 = 0)
    (ha' : a' % 2 = 0) : (a / 2) % 2 ^ k = (a' / 2) % 2 ^ k := by
  have h2k : (0 : Int) < 2 ^ k := by positivity
  obtain ⟨c, hc⟩ : (2 ^ (k + 1) : Int) ∣ a' - a := Int.ModEq.dvd h
  have e1 : a = 2 * (a / 2) := (Int.mul_ediv_cancel' (by omega)).symm
  have e2 : a' = 2 * (a' / 2) := (Int.mul_ediv_cancel' (by omega)).symm
  have : a' / 2 - a / 2 = 2 ^ k * c := by
    have : 2 * (a' / 2 - a / 2) = 2 * (2 ^ k * c) := by rw [pow_succ] at hc; linarith
    exact mul_left_cancel₀ (by norm_num) this
  exact Int.modEq_of_dvd ⟨c, this⟩

theorem mstep_cong {t t' : VG.Proof.Divstep.MSt} {k : Nat} (ht : t.f % 2 = 1) (h : t.cong t' (k + 1)) :
    (VG.Proof.Divstep.mstep t).cong (VG.Proof.Divstep.mstep t') k := by
  obtain ⟨hd, hu, hv, hq, hr, hf, hg⟩ := h
  -- `g mod 2` and `f mod 2` agree.
  have hg2 : t.g % 2 = t'.g % 2 := by
    have := congrArg (· % 2) hg
    simp only [Int.emod_emod_of_dvd _ (show (2 : Int) ∣ 2 ^ (k + 1) by
      exact dvd_pow_self 2 (by omega))] at this
    exact this
  have hf2 : t.f % 2 = t'.f % 2 := by
    have := congrArg (· % 2) hf
    simp only [Int.emod_emod_of_dvd _ (show (2 : Int) ∣ 2 ^ (k + 1) by
      exact dvd_pow_self 2 (by omega))] at this
    exact this
  have hk : (2 : Int) ^ k ∣ 2 ^ (k + 1) := pow_dvd_pow 2 (by omega)
  have hfk : t.f % 2 ^ k = t'.f % 2 ^ k := by
    rw [← Int.emod_emod_of_dvd t.f hk, ← Int.emod_emod_of_dvd t'.f hk, hf]
  unfold VG.Proof.Divstep.mstep MSt.cong
  rw [hd, hg2]
  split
  · rename_i hc
    refine ⟨rfl, by rw [hq], by rw [hr], by rw [hq, hu], by rw [hr, hv], ?_, ?_⟩
    · rw [← Int.emod_emod_of_dvd t.g hk, ← Int.emod_emod_of_dvd t'.g hk, hg]
    · refine VG.Proof.Divstep.half_cong ?_ (by omega) (by omega)
      rw [Int.sub_emod, hg, hf, ← Int.sub_emod]
  · refine ⟨rfl, by rw [hu], by rw [hv], by rw [hq, hu], by rw [hr, hv], hfk, ?_⟩
    rcases Int.emod_two_eq_zero_or_one t'.g with h0 | h0
    · simp only [h0, zero_mul, add_zero]
      exact VG.Proof.Divstep.half_cong hg (by omega) (by omega)
    · simp only [h0, one_mul]
      refine VG.Proof.Divstep.half_cong ?_ (by omega) (by omega)
      rw [Int.add_emod, hg, hf, ← Int.add_emod]

/-- `n ≤ N` steps on `f`, `g` modulo `2^N` give the same `d` and matrix. -/
theorem msteps_cong {t t' : VG.Proof.Divstep.MSt} {N : Nat} (ht : t.f % 2 = 1) (h : t.cong t' N) :
    ∀ n ≤ N, (VG.Proof.Divstep.msteps n t).cong (VG.Proof.Divstep.msteps n t') (N - n)
  | 0, _ => by simpa [VG.Proof.Divstep.msteps] using h
  | n + 1, hn => by
    rw [VG.Proof.Divstep.msteps_succ, VG.Proof.Divstep.msteps_succ]
    have := VG.Proof.Divstep.msteps_cong ht h n (by omega)
    rw [show N - n = (N - (n + 1)) + 1 by omega] at this
    exact VG.Proof.Divstep.mstep_cong (VG.Proof.Divstep.msteps_f_odd ht n) this

end VG.Proof.Divstep

end

/- Proofs formerly in `VerifiedGarbage.Proof.Divstep.Word`. -/
section

/-!
# Divsteps on 64-bit words

A divstep with its matrix on words (`wstep`), without branches: with the
masks `B` (all ones if `g` is odd) and `S = B` and `d ≥ 0`, `(x ^ S) - S` is
`-x` or `x`, so `g + ((f ^ S) - S) & B` is `g - f`, `g + f` or `g`, and
`f + (g' & S)` swaps. On words that hold `d` and the matrix and agree with
`f` and `g` on their low `k + 1` bits, it gives the next state, agreeing on
`k` bits (`wstep_rel`); so `n ≤ 64` steps from the low words of `f` and `g`
give `d` and the matrix of `n` divsteps (`wsteps_rel`).
-/

namespace VG.Proof.Divstep

/-- The words of a step: `d`, the low bits of `f` and `g`, and the matrix. -/
structure WSt where
  D : BitVec 64
  F : BitVec 64
  G : BitVec 64
  U : BitVec 64
  V : BitVec 64
  Q : BitVec 64
  R : BitVec 64

/-- A divstep on words. -/
def wstep (w : VG.Proof.Divstep.WSt) : VG.Proof.Divstep.WSt :=
  let B := 0 - (w.G &&& 1)
  let S := ((w.D >>> 63) - 1) &&& B
  let G1 := w.G + (((w.F ^^^ S) - S) &&& B)
  let Q1 := w.Q + (((w.U ^^^ S) - S) &&& B)
  let R1 := w.R + (((w.V ^^^ S) - S) &&& B)
  ⟨((w.D ^^^ S) - S) + 2, w.F + (G1 &&& S), G1 >>> 1, (w.U + (Q1 &&& S)) <<< 1,
    (w.V + (R1 &&& S)) <<< 1, Q1, R1⟩

/-- `n` such steps. -/
def wsteps : Nat → VG.Proof.Divstep.WSt → VG.Proof.Divstep.WSt
  | 0, w => w
  | n + 1, w => VG.Proof.Divstep.wsteps n (VG.Proof.Divstep.wstep w)

/-- Words holding `d` and the matrix of `t`, and `f`, `g` modulo `2^k`. -/
def WSt.rel (w : VG.Proof.Divstep.WSt) (t : VG.Proof.Divstep.MSt) (k : Nat) : Prop :=
  w.D = BitVec.ofInt 64 t.d ∧ w.U = BitVec.ofInt 64 t.u ∧ w.V = BitVec.ofInt 64 t.v ∧
    w.Q = BitVec.ofInt 64 t.q ∧ w.R = BitVec.ofInt 64 t.r ∧
    (w.F.toNat : Int) % 2 ^ k = t.f % 2 ^ k ∧ (w.G.toNat : Int) % 2 ^ k = t.g % 2 ^ k

theorem ofInt_sub' (a b : Int) : BitVec.ofInt 64 (a - b) = BitVec.ofInt 64 a - BitVec.ofInt 64 b := by
  rw [sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

theorem shl1 (x : BitVec 64) : x <<< 1 = x + x := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, Nat.shiftLeft_eq, Nat.pow_one]
  congr 1; omega

theorem ofInt_two_mul (a : Int) : BitVec.ofInt 64 (2 * a) = BitVec.ofInt 64 a <<< 1 := by
  rw [VG.Proof.Divstep.shl1, two_mul, BitVec.ofInt_add]

/-- Congruence modulo `2^k` (`k ≤ 64`) of a word's value and an integer it is
congruent to modulo `2^64`. -/
theorem toNat_cong {x : BitVec 64} {a : Int} {k : Nat} (hk : k ≤ 64)
    (h : (x.toNat : Int) % 2 ^ 64 = a % 2 ^ 64) : (x.toNat : Int) % 2 ^ k = a % 2 ^ k := by
  have hd : (2 : Int) ^ k ∣ 2 ^ 64 := pow_dvd_pow 2 hk
  rw [← Int.emod_emod_of_dvd _ hd, h, Int.emod_emod_of_dvd _ hd]

theorem lowered {x : BitVec 64} {a : Int} {k : Nat} (h : (x.toNat : Int) % 2 ^ (k + 1) = a % 2 ^ (k + 1)) :
    (x.toNat : Int) % 2 ^ k = a % 2 ^ k := by
  have hd : (2 : Int) ^ k ∣ 2 ^ (k + 1) := pow_dvd_pow 2 (by omega)
  rw [← Int.emod_emod_of_dvd _ hd, h, Int.emod_emod_of_dvd _ hd]

/-- `x - y` as an integer modulo `2^64`. -/
theorem toNat_sub_cong (x y : BitVec 64) :
    ((x - y).toNat : Int) % 2 ^ 64 = ((x.toNat : Int) - y.toNat) % 2 ^ 64 := by
  rw [BitVec.toNat_sub]
  have := y.isLt
  push_cast
  rw [Int.emod_emod_of_dvd _ (by norm_num)]
  omega

theorem toNat_add_cong (x y : BitVec 64) :
    ((x + y).toNat : Int) % 2 ^ 64 = ((x.toNat : Int) + y.toNat) % 2 ^ 64 := by
  rw [BitVec.toNat_add]; push_cast; rw [Int.emod_emod_of_dvd _ (by norm_num)]

/-- Halving a word whose value is congruent to an even integer. -/
theorem half_word {x : BitVec 64} {a : Int} {k : Nat} (hk : k + 1 ≤ 64)
    (h : (x.toNat : Int) % 2 ^ (k + 1) = a % 2 ^ (k + 1)) (ha : a % 2 = 0) :
    ((x >>> 1).toNat : Int) % 2 ^ k = (a / 2) % 2 ^ k := by
  have hx2 : (x.toNat : Int) % 2 = 0 := by
    have := congrArg (· % 2) h
    simp only [Int.emod_emod_of_dvd _ (show (2 : Int) ∣ 2 ^ (k + 1) from dvd_pow_self 2 (by omega))] at this
    omega
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have : ((x.toNat / 2 : Nat) : Int) = (x.toNat : Int) / 2 := by push_cast; rfl
  rw [this]
  exact VG.Proof.Divstep.half_cong h hx2 ha

theorem wsteps_succ (n : Nat) (w : VG.Proof.Divstep.WSt) : VG.Proof.Divstep.wsteps (n + 1) w = VG.Proof.Divstep.wstep (VG.Proof.Divstep.wsteps n w) := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih => rw [VG.Proof.Divstep.wsteps, ih, VG.Proof.Divstep.wsteps]

/-! The three kinds of step, on words. -/

theorem c_allOnes : (0 : BitVec 64) - 1 = BitVec.allOnes 64 := by decide
theorem c_one : (1 : BitVec 64) - 1 = 0 := by decide
theorem c_zero : (0 : BitVec 64) - 0 = 0 := by decide
theorem and0 (x : BitVec 64) : x &&& 0 = 0 := by simp
theorem and0' (x : BitVec 64) : 0 &&& x = 0 := by simp
theorem xor0 (x : BitVec 64) : x ^^^ 0 = x := by simp
theorem ofInt_two : BitVec.ofInt 64 2 = 2 := by decide
theorem two64 : (2#64 : BitVec 64) = 2 := rfl

theorem sub0 (x : BitVec 64) : x - 0 = x := by simp
theorem add0 (x : BitVec 64) : x + 0 = x := by simp

theorem neg_sel (X : BitVec 64) : (X ^^^ BitVec.allOnes 64) - BitVec.allOnes 64 = -X := by
  rw [BitVec.xor_allOnes, BitVec.neg_eq_not_add]
  have : BitVec.allOnes 64 = -1 := by decide
  rw [this, BitVec.sub_neg]; rfl

/-- `g` odd and `d ≥ 0`: the swap. -/
theorem wstep_swap (w : VG.Proof.Divstep.WSt) (hB : w.G &&& 1 = 1) (hS : w.D >>> 63 = 0) :
    VG.Proof.Divstep.wstep w = ⟨-w.D + 2, w.G, (w.G - w.F) >>> 1, w.Q <<< 1, w.R <<< 1, w.Q - w.U, w.R - w.V⟩ := by
  simp only [VG.Proof.Divstep.wstep, hB, hS, VG.Proof.Divstep.c_allOnes, BitVec.and_allOnes, VG.Proof.Divstep.neg_sel, WSt.mk.injEq]
  refine ⟨trivial, by ring, by rw [show w.G + -w.F = w.G - w.F by ring], by rw [show w.U + (w.Q + -w.U) = w.Q by ring],
    by rw [show w.V + (w.R + -w.V) = w.R by ring], by ring, by ring⟩

/-- `g` odd and `d < 0`: `g + f`. -/
theorem wstep_odd (w : VG.Proof.Divstep.WSt) (hB : w.G &&& 1 = 1) (hS : w.D >>> 63 = 1) :
    VG.Proof.Divstep.wstep w = ⟨w.D + 2, w.F, (w.G + w.F) >>> 1, w.U <<< 1, w.V <<< 1, w.Q + w.U, w.R + w.V⟩ := by
  simp only [VG.Proof.Divstep.wstep, hB, hS, VG.Proof.Divstep.c_allOnes, VG.Proof.Divstep.c_one, VG.Proof.Divstep.and0, VG.Proof.Divstep.xor0, BitVec.and_allOnes, VG.Proof.Divstep.sub0, VG.Proof.Divstep.add0]

/-- `g` even. -/
theorem wstep_even (w : VG.Proof.Divstep.WSt) (hB : w.G &&& 1 = 0) :
    VG.Proof.Divstep.wstep w = ⟨w.D + 2, w.F, w.G >>> 1, w.U <<< 1, w.V <<< 1, w.Q, w.R⟩ := by
  simp only [VG.Proof.Divstep.wstep, hB, VG.Proof.Divstep.and0, VG.Proof.Divstep.xor0, VG.Proof.Divstep.sub0, VG.Proof.Divstep.add0]

/-- `G & 1` is `G`'s low bit. -/
theorem and_one_word (x : BitVec 64) : x &&& 1 = if x.toNat % 2 = 1 then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]
  split <;> simp_all

/-- `D >>> 63` is `D`'s sign, for `|d| < 2^63`. -/
theorem sign_word {d : Int} (hd : |d| < 2 ^ 62) : BitVec.ofInt 64 d >>> 63 = if d < 0 then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofInt, Nat.shiftRight_eq_div_pow]
  rw [abs_lt] at hd
  push_cast
  split <;> simp only [BitVec.toNat_ofNat] <;> omega

/-- A divstep on words. -/
theorem wstep_rel {w : VG.Proof.Divstep.WSt} {t : VG.Proof.Divstep.MSt} {k : Nat} (hk : k + 1 ≤ 64) (h : w.rel t (k + 1))
    (hd : |t.d| < 2 ^ 62) (hf : t.f % 2 = 1) : (VG.Proof.Divstep.wstep w).rel (VG.Proof.Divstep.mstep t) k := by
  obtain ⟨hD, hU, hV, hQ, hR, hF, hG⟩ := h
  have hpar : ∀ x : BitVec 64, ∀ a : Int, (x.toNat : Int) % 2 ^ (k + 1) = a % 2 ^ (k + 1) →
      (x.toNat : Int) % 2 = a % 2 := fun x a hx => by
    have := congrArg (· % 2) hx
    simpa only [Int.emod_emod_of_dvd _ (show (2 : Int) ∣ 2 ^ (k + 1) from dvd_pow_self 2 (by omega))] using this
  have gG := hpar _ _ hG
  have hS := VG.Proof.Divstep.sign_word hd
  rw [← hD] at hS
  have hB := VG.Proof.Divstep.and_one_word w.G
  have hd' : (2 : Int) ^ (k + 1) ∣ 2 ^ 64 := pow_dvd_pow 2 hk
  unfold VG.Proof.Divstep.mstep
  by_cases hg : t.g % 2 = 1
  · rw [VG.Proof.Divstep.ite_t (show w.G.toNat % 2 = 1 by omega)] at hB
    by_cases hd0 : 0 ≤ t.d
    · rw [VG.Proof.Divstep.ite_f (show ¬ t.d < 0 by omega)] at hS
      rw [VG.Proof.Divstep.wstep_swap w hB hS, VG.Proof.Divstep.ite_t ⟨hd0, hg⟩]
      refine ⟨?_, ?_, ?_, ?_, ?_, VG.Proof.Divstep.lowered hG, VG.Proof.Divstep.half_word hk ?_ (by omega)⟩
      · simp only; rw [hD, VG.Proof.Divstep.ofInt_sub', VG.Proof.Divstep.ofInt_two]; ring
      · simp only; rw [hQ, VG.Proof.Divstep.ofInt_two_mul]
      · simp only; rw [hR, VG.Proof.Divstep.ofInt_two_mul]
      · simp only; rw [hQ, hU, VG.Proof.Divstep.ofInt_sub']
      · simp only; rw [hR, hV, VG.Proof.Divstep.ofInt_sub']
      · rw [← Int.emod_emod_of_dvd _ hd', VG.Proof.Divstep.toNat_sub_cong, Int.emod_emod_of_dvd _ hd', Int.sub_emod, hG, hF,
          ← Int.sub_emod]
    · rw [VG.Proof.Divstep.ite_t (show t.d < 0 by omega)] at hS
      rw [VG.Proof.Divstep.wstep_odd w hB hS, VG.Proof.Divstep.ite_f (show ¬ (0 ≤ t.d ∧ t.g % 2 = 1) by omega)]
      refine ⟨?_, ?_, ?_, ?_, ?_, VG.Proof.Divstep.lowered hF, ?_⟩
      · simp only; rw [hD, BitVec.ofInt_add, BitVec.ofInt_ofNat, VG.Proof.Divstep.two64]; ring
      · simp only; rw [hU, VG.Proof.Divstep.ofInt_two_mul]
      · simp only; rw [hV, VG.Proof.Divstep.ofInt_two_mul]
      · simp only; rw [hQ, hU, hg, one_mul, BitVec.ofInt_add]
      · simp only; rw [hR, hV, hg, one_mul, BitVec.ofInt_add]
      · simp only; rw [hg, one_mul]
        refine VG.Proof.Divstep.half_word hk ?_ (by omega)
        rw [← Int.emod_emod_of_dvd _ hd', VG.Proof.Divstep.toNat_add_cong, Int.emod_emod_of_dvd _ hd', Int.add_emod, hG, hF,
          ← Int.add_emod]
  · have hg0 : t.g % 2 = 0 := by omega
    rw [VG.Proof.Divstep.ite_f (show ¬ w.G.toNat % 2 = 1 by omega)] at hB
    rw [VG.Proof.Divstep.wstep_even w hB, VG.Proof.Divstep.ite_f (show ¬ (0 ≤ t.d ∧ t.g % 2 = 1) by omega)]
    refine ⟨?_, ?_, ?_, ?_, ?_, VG.Proof.Divstep.lowered hF, ?_⟩
    · simp only; rw [hD, BitVec.ofInt_add, BitVec.ofInt_ofNat, VG.Proof.Divstep.two64]; ring
    · simp only; rw [hU, VG.Proof.Divstep.ofInt_two_mul]
    · simp only; rw [hV, VG.Proof.Divstep.ofInt_two_mul]
    · simp only; rw [hQ, hg0, zero_mul, add_zero]
    · simp only; rw [hR, hg0, zero_mul, add_zero]
    · simp only; rw [hg0, zero_mul, add_zero]; exact VG.Proof.Divstep.half_word hk hG hg0

/-- `n ≤ K` steps on words agreeing on `K ≤ 64` bits. -/
theorem wsteps_rel {w : VG.Proof.Divstep.WSt} {t : VG.Proof.Divstep.MSt} {K : Nat} (hK : K ≤ 64) (h : w.rel t K)
    (hd : |t.d| + 2 * K < 2 ^ 62) (hf : t.f % 2 = 1) : ∀ n ≤ K, (VG.Proof.Divstep.wsteps n w).rel (VG.Proof.Divstep.msteps n t) (K - n)
  | 0, _ => by simpa [VG.Proof.Divstep.wsteps, VG.Proof.Divstep.msteps] using h
  | n + 1, hn => by
    have ih := VG.Proof.Divstep.wsteps_rel hK h hd hf n (by omega)
    rw [VG.Proof.Divstep.wsteps_succ, VG.Proof.Divstep.msteps_succ]
    rw [show K - n = (K - (n + 1)) + 1 by omega] at ih
    refine VG.Proof.Divstep.wstep_rel (by omega) ih ?_ (VG.Proof.Divstep.msteps_f_odd hf n)
    have := VG.Proof.Divstep.msteps_d t n
    have : (2 * n : Int) ≤ 2 * K := by exact_mod_cast (by omega : 2 * n ≤ 2 * K)
    linarith

end VG.Proof.Divstep

end

/- Proofs formerly in `VerifiedGarbage.Proof.Divstep.Alg`. -/
section

/-!
# Inversion by batches of divsteps

The inverse of `x` modulo an odd `p` (`0 ≤ x < p`), as the code computes it
(`invRun`): from `(d, f, g) = (1, p, x)` and coefficients `(a, b) = (0, 1)`,
each batch takes the matrix `(u, v, q, r)` of `N` divsteps, replaces
`(f, g)` by `(u f + v g, q f + r g) / 2^N` (exactly: `batch_dfg`), and
`(a, b)` by `(u a + v b, q a + r b) / 2^64 mod p` (`mred`, adding the multiple
of `p` that clears the low word, then at most one `p` back into `[0, p)`).
With `f ≡ x a 2^(c i)` and `g ≡ x b 2^(c i)` modulo `p`, `c = 64 - N`
(`invRun_inv`), once `g = 0`, `f = ±gcd(p, x) = ±1`, and
`x (± a) 2^(c i) ≡ 1` (`invRun_spec`).
-/

namespace VG.Proof.Divstep

/-- `t / 2^64 mod p`: `t` plus the multiple `k p` (`k = t m mod 2^64`, for
`m = -p⁻¹ mod 2^64`) that clears its low word, over `2^64`. -/
def mredRaw (p m t : Int) : Int := (t + (t * m) % 2 ^ 64 * p) / 2 ^ 64

/-- Into `[0, p)` from `(-p, 2p)`. -/
def norm (p t : Int) : Int := if t < 0 then t + p else if p ≤ t then t - p else t

def mred (p m t : Int) : Int := VG.Proof.Divstep.norm p (VG.Proof.Divstep.mredRaw p m t)

/-- The state of the inversion. -/
structure IState where
  d : Int
  f : Int
  g : Int
  a : Int
  b : Int

/-- A batch of `N` divsteps. -/
def batch (N : Nat) (p m : Int) (s : VG.Proof.Divstep.IState) : VG.Proof.Divstep.IState :=
  let t := VG.Proof.Divstep.msteps N (MSt.init s.d s.f s.g)
  ⟨t.d, (t.u * s.f + t.v * s.g) / 2 ^ N, (t.q * s.f + t.r * s.g) / 2 ^ N,
    VG.Proof.Divstep.mred p m (t.u * s.a + t.v * s.b), VG.Proof.Divstep.mred p m (t.q * s.a + t.r * s.b)⟩

/-- `B` batches from the start. -/
def invRun (N : Nat) (p m x : Int) : Nat → VG.Proof.Divstep.IState
  | 0 => ⟨1, p, x, 0, 1⟩
  | B + 1 => VG.Proof.Divstep.batch N p m (VG.Proof.Divstep.invRun N p m x B)

/-- A batch's `(d, f, g)` are `N` divsteps'. -/
theorem batch_dfg {N : Nat} {p m : Int} {s : VG.Proof.Divstep.IState} (hf : s.f % 2 = 1) :
    ((VG.Proof.Divstep.batch N p m s).d, (VG.Proof.Divstep.batch N p m s).f, (VG.Proof.Divstep.batch N p m s).g) = VG.Proof.Divstep.divsteps N (s.d, s.f, s.g) := by
  have hdfg := VG.Proof.Divstep.msteps_dfg N (MSt.init s.d s.f s.g)
  simp only [MSt.init] at hdfg
  rw [← hdfg]
  have hm := VG.Proof.Divstep.msteps_mat (d := s.d) (g := s.g) hf N
  obtain ⟨h1, h2⟩ := hm
  simp only [VG.Proof.Divstep.batch, MSt.init] at h1 h2 ⊢
  have hpos : (0 : Int) < 2 ^ N := by positivity
  rw [← h1, ← h2, Int.mul_ediv_cancel_left _ hpos.ne', Int.mul_ediv_cancel_left _ hpos.ne']

/-- `B` batches are `N B` divsteps. -/
theorem invRun_dfg {N : Nat} {p m x : Int} (hp : p % 2 = 1) :
    ∀ B, ((VG.Proof.Divstep.invRun N p m x B).d, (VG.Proof.Divstep.invRun N p m x B).f, (VG.Proof.Divstep.invRun N p m x B).g) = VG.Proof.Divstep.divsteps (N * B) (1, p, x) ∧
      (VG.Proof.Divstep.invRun N p m x B).f % 2 = 1
  | 0 => ⟨rfl, hp⟩
  | B + 1 => by
    obtain ⟨ih, hodd⟩ := VG.Proof.Divstep.invRun_dfg (N := N) (m := m) (x := x) hp B
    have e := VG.Proof.Divstep.batch_dfg (N := N) (p := p) (m := m) hodd
    simp only [VG.Proof.Divstep.invRun]
    rw [e, ih, show N * (B + 1) = N * B + N by ring, VG.Proof.Divstep.divsteps_add]
    refine ⟨rfl, ?_⟩
    have h := (VG.Proof.Divstep.divsteps_odd (d := 1) (f := p) (g := x) (by decide) hp (N * B + N)).2
    rw [VG.Proof.Divstep.divsteps_add, ← ih, ← e] at h
    exact h

/-- `mredRaw` is exact: `2^64 · mredRaw t = t + k p`, with `k = t m mod 2^64`. -/
theorem mredRaw_spec {p m t : Int} (hm : (p * m + 1) % 2 ^ 64 = 0) :
    2 ^ 64 * VG.Proof.Divstep.mredRaw p m t = t + (t * m) % 2 ^ 64 * p := by
  unfold VG.Proof.Divstep.mredRaw
  apply Int.mul_ediv_cancel'
  -- `t + (t m mod 2^64) p ≡ t + t m p = t (1 + p m) ≡ 0`.
  have h1 : (2 : Int) ^ 64 ∣ p * m + 1 := Int.dvd_of_emod_eq_zero hm
  have h2 : (2 : Int) ^ 64 ∣ t * m - (t * m) % 2 ^ 64 := by
    have := Int.emod_add_ediv_mul (t * m) (2 ^ 64)
    exact ⟨(t * m) / 2 ^ 64, by linarith⟩
  have : t + (t * m) % 2 ^ 64 * p = t * (p * m + 1) - (t * m - (t * m) % 2 ^ 64) * p := by ring
  rw [this]
  exact dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_left h2 _)

/-- `2^64 mred t ≡ t` modulo `p`. -/
theorem mred_cong {p m t : Int} (hm : (p * m + 1) % 2 ^ 64 = 0) :
    2 ^ 64 * VG.Proof.Divstep.mred p m t ≡ t [ZMOD p] := by
  have hraw : 2 ^ 64 * VG.Proof.Divstep.mredRaw p m t ≡ t [ZMOD p] := by
    rw [VG.Proof.Divstep.mredRaw_spec hm]; exact Int.add_mul_emod_self_right _ _ _
  have hp0 : 2 ^ 64 * p ≡ 0 [ZMOD p] := Int.modEq_zero_iff_dvd.mpr (dvd_mul_left p _)
  unfold VG.Proof.Divstep.mred VG.Proof.Divstep.norm
  split
  · rw [mul_add]; simpa using hraw.add hp0
  · split
    · rw [mul_sub]; simpa using hraw.sub hp0
    · exact hraw

/-- `mred t` is in `[0, p)` for `|t| < 2^63 p` (with `0 ≤ k < 2^64`). -/
theorem mred_range {p m t : Int} (hp : 0 < p) (hm : (p * m + 1) % 2 ^ 64 = 0) (ht : |t| ≤ 2 ^ 63 * p) :
    0 ≤ VG.Proof.Divstep.mred p m t ∧ VG.Proof.Divstep.mred p m t < p := by
  have hraw := VG.Proof.Divstep.mredRaw_spec (t := t) hm
  have hk0 : 0 ≤ (t * m) % 2 ^ 64 := Int.emod_nonneg _ (by norm_num)
  have hk1 : (t * m) % 2 ^ 64 < 2 ^ 64 := Int.emod_lt_of_pos _ (by norm_num)
  rw [abs_le] at ht
  -- `-p < mredRaw t < 2p`.
  have lo : -p < VG.Proof.Divstep.mredRaw p m t := by
    by_contra h; push Not at h
    have : 2 ^ 64 * VG.Proof.Divstep.mredRaw p m t ≤ 2 ^ 64 * (-p) := by nlinarith
    nlinarith
  have hi : VG.Proof.Divstep.mredRaw p m t < 2 * p := by
    by_contra h; push Not at h
    have : 2 ^ 64 * (2 * p) ≤ 2 ^ 64 * VG.Proof.Divstep.mredRaw p m t := by nlinarith
    nlinarith
  unfold VG.Proof.Divstep.mred VG.Proof.Divstep.norm
  split
  · constructor <;> linarith
  · split <;> constructor <;> linarith

/-- The invariant: `f ≡ x a 2^(c i)`, `g ≡ x b 2^(c i)` modulo `p`, `c = 64 - N`, and
`a`, `b` in `[0, p)`. -/
def IState.inv (s : VG.Proof.Divstep.IState) (p x : Int) (K : Int) : Prop :=
  s.f ≡ x * s.a * K [ZMOD p] ∧ s.g ≡ x * s.b * K [ZMOD p] ∧ 0 ≤ s.a ∧ s.a < p ∧ 0 ≤ s.b ∧ s.b < p

/-- `2` is invertible modulo an odd `p`: cancel powers of 2. -/
theorem cancel_pow2 {p a b : Int} {N : Nat} (hp : p % 2 = 1) (hp0 : 0 < p) (h : 2 ^ N * a ≡ 2 ^ N * b [ZMOD p]) :
    a ≡ b [ZMOD p] := by
  have hc : Int.gcd p (2 ^ N) = 1 := Int.gcd_pow_right_of_gcd_eq_one (VG.Proof.Divstep.gcd_two hp)
  have := Int.ModEq.cancel_left_div_gcd (by omega) h
  rwa [hc, Int.ofNat_one, Int.ediv_one] at this

theorem batch_inv {N : Nat} (hN : N ≤ 62) {p m x K : Int} (hp : p % 2 = 1) (hp0 : 0 < p)
    (hm : (p * m + 1) % 2 ^ 64 = 0) {s : VG.Proof.Divstep.IState} (hf : s.f % 2 = 1) (h : s.inv p x K) :
    (VG.Proof.Divstep.batch N p m s).inv p x (K * 2 ^ (64 - N)) := by
  obtain ⟨hF, hG, a0, a1, b0, b1⟩ := h
  have hmat := VG.Proof.Divstep.msteps_mat (d := s.d) (g := s.g) hf N
  have hb := VG.Proof.Divstep.msteps_bnd s.d s.f s.g N
  obtain ⟨h1, h2⟩ := hmat
  obtain ⟨bu, bq⟩ := hb
  set t := VG.Proof.Divstep.msteps N (MSt.init s.d s.f s.g) with ht
  have hpos : (0 : Int) < 2 ^ N := by positivity
  have ef : 2 ^ N * ((t.u * s.f + t.v * s.g) / 2 ^ N) = t.u * s.f + t.v * s.g := by
    rw [← h1, Int.mul_ediv_cancel_left _ hpos.ne']
  have eg : 2 ^ N * ((t.q * s.f + t.r * s.g) / 2 ^ N) = t.q * s.f + t.r * s.g := by
    rw [← h2, Int.mul_ediv_cancel_left _ hpos.ne']
  -- The coefficients' products are small.
  have small : ∀ y z : Int, |y| + |z| ≤ 2 ^ N → |y * s.a + z * s.b| ≤ 2 ^ 63 * p := by
    intro y z hyz
    have : |y * s.a + z * s.b| ≤ |y| * p + |z| * p := by
      calc |y * s.a + z * s.b| ≤ |y * s.a| + |z * s.b| := abs_add_le _ _
        _ = |y| * |s.a| + |z| * |s.b| := by rw [abs_mul, abs_mul]
        _ ≤ |y| * p + |z| * p := by
          rw [abs_of_nonneg a0, abs_of_nonneg b0]
          exact add_le_add (mul_le_mul_of_nonneg_left a1.le (abs_nonneg _))
            (mul_le_mul_of_nonneg_left b1.le (abs_nonneg _))
    have h62 : (2 : Int) ^ N ≤ 2 ^ 63 := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  have rA := VG.Proof.Divstep.mred_range hp0 hm (small t.u t.v bu)
  have rB := VG.Proof.Divstep.mred_range hp0 hm (small t.q t.r bq)
  have cA := VG.Proof.Divstep.mred_cong (p := p) (t := t.u * s.a + t.v * s.b) hm
  have cB := VG.Proof.Divstep.mred_cong (p := p) (t := t.q * s.a + t.r * s.b) hm
  have e64 : (2 : Int) ^ 64 = 2 ^ N * 2 ^ (64 - N) := by rw [← pow_add]; congr 1; omega
  refine ⟨?_, ?_, rA.1, rA.2, rB.1, rB.2⟩
  · apply VG.Proof.Divstep.cancel_pow2 (N := N) hp hp0
    show 2 ^ N * ((t.u * s.f + t.v * s.g) / 2 ^ N) ≡ _ [ZMOD p]
    rw [ef]
    calc t.u * s.f + t.v * s.g ≡ t.u * (x * s.a * K) + t.v * (x * s.b * K) [ZMOD p] :=
          (hF.mul_left _).add (hG.mul_left _)
      _ = x * K * (t.u * s.a + t.v * s.b) := by ring
      _ ≡ x * K * (2 ^ 64 * VG.Proof.Divstep.mred p m (t.u * s.a + t.v * s.b)) [ZMOD p] := (cA.symm.mul_left _)
      _ = 2 ^ N * (x * VG.Proof.Divstep.mred p m (t.u * s.a + t.v * s.b) * (K * 2 ^ (64 - N))) := by rw [e64]; ring
  · apply VG.Proof.Divstep.cancel_pow2 (N := N) hp hp0
    show 2 ^ N * ((t.q * s.f + t.r * s.g) / 2 ^ N) ≡ _ [ZMOD p]
    rw [eg]
    calc t.q * s.f + t.r * s.g ≡ t.q * (x * s.a * K) + t.r * (x * s.b * K) [ZMOD p] :=
          (hF.mul_left _).add (hG.mul_left _)
      _ = x * K * (t.q * s.a + t.r * s.b) := by ring
      _ ≡ x * K * (2 ^ 64 * VG.Proof.Divstep.mred p m (t.q * s.a + t.r * s.b)) [ZMOD p] := (cB.symm.mul_left _)
      _ = 2 ^ N * (x * VG.Proof.Divstep.mred p m (t.q * s.a + t.r * s.b) * (K * 2 ^ (64 - N))) := by rw [e64]; ring

/-- The invariant through `B` batches. -/
theorem invRun_inv {N : Nat} (hN : N ≤ 62) {p m x : Int} (hp : p % 2 = 1) (hp1 : 1 < p)
    (hm : (p * m + 1) % 2 ^ 64 = 0) : ∀ B, (VG.Proof.Divstep.invRun N p m x B).inv p x (2 ^ ((64 - N) * B))
  | 0 => by
    refine ⟨?_, ?_, le_refl _, by simp only [VG.Proof.Divstep.invRun]; omega, by simp [VG.Proof.Divstep.invRun], by simp only [VG.Proof.Divstep.invRun]; omega⟩
    · simp only [VG.Proof.Divstep.invRun, mul_zero, pow_zero, mul_one]
      exact Int.emod_self.trans (by simp)
    · simp [VG.Proof.Divstep.invRun, Int.ModEq]
  | B + 1 => by
    have := VG.Proof.Divstep.batch_inv hN hp (by omega) hm ((VG.Proof.Divstep.invRun_dfg (N := N) (m := m) (x := x) hp B).2) (VG.Proof.Divstep.invRun_inv hN hp hp1 hm B)
    simp only [VG.Proof.Divstep.invRun]
    rw [show (64 - N) * (B + 1) = (64 - N) * B + (64 - N) by ring, pow_add]
    exact this

/-- After enough batches, `f = ±1` and `x (± a) 2^(c B) ≡ 1` modulo `p`, if
`gcd(p, x) = 1`. -/
theorem invRun_spec {N B : Nat} (hN : N ≤ 62) {p m x : Int} (hp : p % 2 = 1) (hp1 : 1 < p)
    (hm : (p * m + 1) % 2 ^ 64 = 0)
    (hdone : (VG.Proof.Divstep.divsteps (N * B) (1, p, x)).2.2 = 0 ∧ (VG.Proof.Divstep.divsteps (N * B) (1, p, x)).2.1.natAbs = Int.gcd p x)
    (hg : Int.gcd p x = 1) :
    ((VG.Proof.Divstep.invRun N p m x B).f = 1 ∨ (VG.Proof.Divstep.invRun N p m x B).f = -1) ∧
      x * ((VG.Proof.Divstep.invRun N p m x B).f * (VG.Proof.Divstep.invRun N p m x B).a) * 2 ^ ((64 - N) * B) ≡ 1 [ZMOD p] := by
  have hd := (VG.Proof.Divstep.invRun_dfg (N := N) (m := m) (x := x) hp B).1
  have hI := VG.Proof.Divstep.invRun_inv (x := x) hN hp hp1 hm B
  set s := VG.Proof.Divstep.invRun N p m x B
  have hfa : s.f.natAbs = 1 := by
    have : s.f = (VG.Proof.Divstep.divsteps (N * B) (1, p, x)).2.1 := by rw [← hd]
    rw [this, hdone.2, hg]
  have hf1 : s.f = 1 ∨ s.f = -1 := by omega
  refine ⟨hf1, ?_⟩
  -- `f ≡ x a 2^(c B)` and `f² = 1`.
  have := hI.1.mul_left s.f
  have hf2 : s.f * s.f = 1 := by rcases hf1 with h | h <;> rw [h] <;> norm_num
  rw [hf2] at this
  have e : s.f * (x * s.a * 2 ^ ((64 - N) * B)) = x * (s.f * s.a) * 2 ^ ((64 - N) * B) := by ring
  rw [← e]; exact this.symm

end VG.Proof.Divstep

end
