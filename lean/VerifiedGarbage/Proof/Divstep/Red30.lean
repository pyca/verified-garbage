module
public import VerifiedGarbage.Proof.Divstep.Alg32Def
public import VerifiedGarbage.Proof.Divstep.Red30Def

import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Divstep.Alg32
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Linarith.Frontend
import VerifiedGarbage.Proof.Divstep.Tc32Shr
import Mathlib.Algebra.Order.Ring.Abs

/-! # Batches of 30 divsteps with the coefficients reduced by `2^30`

`invRun`'s `(d, f, g)` with coefficients `(a, b)` that each batch replaces by `(u a + v b, q a + r b)`
divided by `2^30` modulo `p` (rather than `invRun`'s `2^32`, `mred`), so that no scale is left at
the end: with `f ≡ x a` and `g ≡ x b` modulo `p` before a batch, they hold after it
(`batch_cong30`). `red30_dvd`: the multiple of `p` that clears the low 30 bits of a number, from
`-p⁻¹ mod 2^32`.
-/

@[expose] public section

namespace VG.Proof.Divstep.W32

/-- A batch of 30 divsteps keeps `f ≡ x a`, `g ≡ x b` modulo `p` for coefficients `a', b'` with
`2^30 a' ≡ u a + v b` and `2^30 b' ≡ q a + r b`. -/
theorem batch_cong30 {p m x a b a' b' : Int} {s : IState} (hp : p % 2 = 1) (hp0 : 0 < p) (hf : s.f % 2 = 1)
    (hF : s.f ≡ x * a [ZMOD p]) (hG : s.g ≡ x * b [ZMOD p])
    (ha : 2 ^ 30 * a' ≡ (msteps 30 (MSt.init s.d s.f s.g)).u * a + (msteps 30 (MSt.init s.d s.f s.g)).v * b
      [ZMOD p])
    (hb : 2 ^ 30 * b' ≡ (msteps 30 (MSt.init s.d s.f s.g)).q * a + (msteps 30 (MSt.init s.d s.f s.g)).r * b
      [ZMOD p]) :
    (batch 30 p m s).f ≡ x * a' [ZMOD p] ∧ (batch 30 p m s).g ≡ x * b' [ZMOD p] := by
  obtain ⟨h1, h2⟩ := msteps_mat (d := s.d) (g := s.g) hf 30
  set t := msteps 30 (MSt.init s.d s.f s.g)
  have hpos : (0 : Int) < 2 ^ 30 := by norm_num
  have ef : 2 ^ 30 * ((t.u * s.f + t.v * s.g) / 2 ^ 30) = t.u * s.f + t.v * s.g := by
    rw [← h1, Int.mul_ediv_cancel_left _ hpos.ne']
  have eg : 2 ^ 30 * ((t.q * s.f + t.r * s.g) / 2 ^ 30) = t.q * s.f + t.r * s.g := by
    rw [← h2, Int.mul_ediv_cancel_left _ hpos.ne']
  refine ⟨cancel_pow2 (N := 30) hp hp0 ?_, cancel_pow2 (N := 30) hp hp0 ?_⟩
  · show 2 ^ 30 * ((t.u * s.f + t.v * s.g) / 2 ^ 30) ≡ _ [ZMOD p]
    rw [ef]
    calc t.u * s.f + t.v * s.g ≡ t.u * (x * a) + t.v * (x * b) [ZMOD p] := (hF.mul_left _).add (hG.mul_left _)
      _ = x * (t.u * a + t.v * b) := by ring
      _ ≡ x * (2 ^ 30 * a') [ZMOD p] := ha.symm.mul_left _
      _ = 2 ^ 30 * (x * a') := by ring
  · show 2 ^ 30 * ((t.q * s.f + t.r * s.g) / 2 ^ 30) ≡ _ [ZMOD p]
    rw [eg]
    calc t.q * s.f + t.r * s.g ≡ t.q * (x * a) + t.r * (x * b) [ZMOD p] := (hF.mul_left _).add (hG.mul_left _)
      _ = x * (t.q * a + t.r * b) := by ring
      _ ≡ x * (2 ^ 30 * b') [ZMOD p] := hb.symm.mul_left _
      _ = 2 ^ 30 * (x * b') := by ring

/-- The digit `q = (t iv mod 2^32) mod 2^30` makes `t + q p` a multiple of `2^30` for
`p iv ≡ -1 (mod 2^32)`. -/
theorem red30_dvd {p iv t : Nat} (h : (p * iv + 1) % 2 ^ 32 = 0) :
    (t + (t % 2 ^ 32 * iv % 2 ^ 32 % 2 ^ 30) * p) % 2 ^ 30 = 0 := by
  have h30 : (p * iv + 1) % 2 ^ 30 = 0 := by
    have := Nat.mod_mod_of_dvd (p * iv + 1) (show 2 ^ 30 ∣ 2 ^ 32 by decide)
    rw [← this, h]; rfl
  have e1 : t % 2 ^ 32 * iv % 2 ^ 32 % 2 ^ 30 = t * iv % 2 ^ 30 := by
    rw [Nat.mod_mod_of_dvd _ (show 2 ^ 30 ∣ 2 ^ 32 by decide), Nat.mul_mod, Nat.mod_mod_of_dvd _
      (show 2 ^ 30 ∣ 2 ^ 32 by decide), ← Nat.mul_mod]
  rw [e1, Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]
  have : t + t * iv * p = t * (p * iv + 1) := by ring
  rw [this, Nat.mul_mod, h30, Nat.mul_zero, Nat.zero_mod]

/-! ## A batch's products on words -/

/-- `|c| T ≡ c x (mod M)` for `T` the negation of `X ≡ x` modulo `M` where `c` is negative. -/
theorem cneg_cong {M : Nat} {c x : Int} {T X : Nat} (hX : (X : Int) % M = x % M)
    (hneg : c < 0 → ∃ b, T + X = 0 + M * b) (hpos : ¬ c < 0 → T = X) :
    ((c.natAbs * T : Nat) : Int) % M = (c * x) % M := by
  by_cases h : c < 0
  · obtain ⟨b, hb⟩ := hneg h
    have e : (T : Int) = -X + M * b := by omega
    push_cast
    rw [abs_of_neg h, e]
    have : -c * (-(X : Int) + M * b) = c * X + M * (-c * b) := by ring
    rw [this, Int.add_mul_emod_self_left, Int.mul_emod, hX, ← Int.mul_emod]
  · rw [hpos h]
    push_cast
    rw [abs_of_nonneg (not_lt.mp h), Int.mul_emod, hX, ← Int.mul_emod]

/-- The new `f` (or `g`) of a batch on words: the products of the magnitudes and the negated factors,
modulo `M = 2 H`, shifted right by 30 with the sign word, is `(u f + v g) / 2^30` modulo `M`. -/
theorem fg_word {H : Nat} {u v f g y z : Int} {F G T₁ T₂ A e D cap : Nat} (hH : 0 < H)
    (hF : (F : Int) % (2 * H : Nat) = f % (2 * H : Nat)) (hG : (G : Int) % (2 * H : Nat) = g % (2 * H : Nat))
    (n₁ : u < 0 → ∃ b, T₁ + F = 0 + 2 * H * b) (p₁ : ¬ u < 0 → T₁ = F)
    (n₂ : v < 0 → ∃ b, T₂ + G = 0 + 2 * H * b) (p₂ : ¬ v < 0 → T₂ = G)
    (hA : A + 2 * H * e = u.natAbs * T₁ + v.natAbs * T₂) (hA' : A < 2 * H)
    (huv : |u| + |v| ≤ 2 ^ 30) (hf : |f| ≤ cap) (hg : |g| ≤ cap) (hcap : 2 ^ 30 * cap < H)
    (hy : y = u * f + v * g) (hz : y = 2 ^ 30 * z)
    (hD : D = (A + 2 * H * (if H ≤ A then 2 ^ 32 - 1 else 0)) / 2 ^ 30 % (2 * H)) :
    (D : Int) % ((2 * H : Nat) : Int) = z % ((2 * H : Nat) : Int) := by
  have c1 := cneg_cong (M := 2 * H) hF (fun h => by obtain ⟨b, hb⟩ := n₁ h; exact ⟨b, hb⟩) p₁
  have c2 := cneg_cong (M := 2 * H) hG (fun h => by obtain ⟨b, hb⟩ := n₂ h; exact ⟨b, hb⟩) p₂
  have hAy : (A : Int) % ((2 * H : Nat) : Int) = y % ((2 * H : Nat) : Int) := by
    have e1 : (A : Int) = ((u.natAbs * T₁ : Nat) : Int) + ((v.natAbs * T₂ : Nat) : Int) - (2 * H : Nat) * e := by
      push_cast; push_cast at hA; linarith
    rw [e1, Int.sub_emod, Int.mul_emod_right, Int.sub_zero, Int.emod_emod_of_dvd _ (dvd_refl _), Int.add_emod,
      c1, c2, ← Int.add_emod, hy]
  have hb : |u * f + v * g| ≤ 2 ^ 30 * cap := by
    have hp : 0 ≤ (cap : Int) := Int.natCast_nonneg _
    calc |u * f + v * g| ≤ |u| * |f| + |v| * |g| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ |u| * cap + |v| * cap := add_le_add (mul_le_mul_of_nonneg_left hf (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hg (abs_nonneg _))
      _ = (|u| + |v|) * cap := by ring
      _ ≤ 2 ^ 30 * cap := mul_le_mul_of_nonneg_right huv hp
  rw [abs_le] at hb
  have hH' : (2 : Int) ^ 30 * cap < H := by exact_mod_cast hcap
  exact shr_nat rfl rfl hH hA' hAy (by rw [hy]; push_cast; linarith) (by rw [hy]; linarith) hz hD

/-- `|c| T ≡ c x (mod p)` for `T` the negation `p - X` of `X < p` where `c` is negative, and
`T ≤ p`. -/
theorem cnegP {p H : Nat} {c : Int} {T X : Nat} (hX : X < p) (hT : T < 2 * H)
    (hneg : c < 0 → ∃ b, T + X = p + 2 * H * b) (hpos : ¬ c < 0 → T = X) :
    T ≤ p ∧ ((c.natAbs * T : Nat) : Int) ≡ c * X [ZMOD p] := by
  by_cases h : c < 0
  · obtain ⟨b, hb⟩ := hneg h
    have b0 : b = 0 := by
      rcases Nat.eq_zero_or_pos b with hb0 | hb0
      · exact hb0
      · have : 2 * H ≤ 2 * H * b := Nat.le_mul_of_pos_right _ hb0
        omega
    subst b0
    have e : (T : Int) = p - X := by omega
    refine ⟨by omega, ?_⟩
    push_cast
    rw [abs_of_neg h, e]
    have : -c * ((p : Int) - X) = c * X + p * (-c) := by ring
    rw [this]
    exact Int.modEq_iff_dvd.mpr ⟨c, by ring⟩
  · rw [hpos h]
    refine ⟨hX.le, ?_⟩
    push_cast
    rw [abs_of_nonneg (not_lt.mp h)]

/-- The new `d` (or `e`) of a batch on words: the products of the magnitudes and the factors
negated modulo `p`, the multiple of `p` that clears the low 30 bits, the shift, and one
conditional subtraction leave `d' < p` with `2^30 d' ≡ u d + v e (mod p)`. -/
theorem de_word {p H iv : Nat} {u v : Int} {D E T₁ T₂ A e q A' c R D' : Nat}
    (hp : p % 2 = 1) (hpH : 2 ^ 31 * p ≤ H) (hiv : (p * iv + 1) % 2 ^ 32 = 0)
    (hD : D < p) (hE : E < p) (hT₁ : T₁ < 2 * H) (hT₂ : T₂ < 2 * H)
    (n₁ : u < 0 → ∃ b, T₁ + D = p + 2 * H * b) (p₁ : ¬ u < 0 → T₁ = D)
    (n₂ : v < 0 → ∃ b, T₂ + E = p + 2 * H * b) (p₂ : ¬ v < 0 → T₂ = E)
    (huv : |u| + |v| ≤ 2 ^ 30) (hA : A + 2 * H * e = u.natAbs * T₁ + v.natAbs * T₂) (hA' : A < 2 * H)
    (hq : q = A % 2 ^ 32 * iv % 2 ^ 32 % 2 ^ 30) (hred : A' + 2 * H * c = A + q * p) (hA'' : A' < 2 * H)
    (hR : R = (A' + 2 * H * (if H ≤ A' then 2 ^ 32 - 1 else 0)) / 2 ^ 30 % (2 * H))
    (hD' : D' = (if R < p then R else R - p) % (2 * H)) :
    D' < p ∧ (2 ^ 30 * D' : Int) ≡ u * D + v * E [ZMOD p] := by
  have hp0 : 0 < p := by omega
  have pH : p ≤ 2 * H := by omega
  obtain ⟨t1, c1⟩ := cnegP hD hT₁ n₁ p₁
  obtain ⟨t2, c2⟩ := cnegP hE hT₂ n₂ p₂
  have hu : u.natAbs + v.natAbs ≤ 2 ^ 30 := by
    have := Int.natCast_natAbs u; have := Int.natCast_natAbs v; omega
  have sum_le : u.natAbs * T₁ + v.natAbs * T₂ ≤ 2 ^ 30 * p := by
    have := Nat.mul_le_mul_left u.natAbs t1
    have := Nat.mul_le_mul_left v.natAbs t2
    have := Nat.mul_le_mul_right p hu
    rw [Nat.add_mul] at this
    omega
  have e0 : e = 0 := by
    rcases Nat.eq_zero_or_pos e with h | h
    · exact h
    · have : 2 * H ≤ 2 * H * e := Nat.le_mul_of_pos_right _ h
      omega
  subst e0
  have hq30 : q < 2 ^ 30 := by rw [hq]; exact Nat.mod_lt _ (by decide)
  have dvd0 : (A + q * p) % 2 ^ 30 = 0 := by rw [hq]; exact red30_dvd hiv
  clear hq
  have qp : q * p ≤ (2 ^ 30 - 1) * p := Nat.mul_le_mul_right _ (by omega)
  have c0 : c = 0 := by
    rcases Nat.eq_zero_or_pos c with h | h
    · exact h
    · have : 2 * H ≤ 2 * H * c := Nat.le_mul_of_pos_right _ h
      omega
  subst c0
  have eA' : A' = A + q * p := by omega
  have eA : A = u.natAbs * T₁ + v.natAbs * T₂ := by omega
  have small : A' < H := by
    rw [eA', eA]
    generalize u.natAbs * T₁ + v.natAbs * T₂ = S at sum_le
    generalize q * p = Q at qp
    omega
  have hR' : R = A' / 2 ^ 30 := by
    rw [hR]; simp only [show ¬ H ≤ A' by omega, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
    exact Nat.mod_eq_of_lt (by omega)
  have dvd : A' % 2 ^ 30 = 0 := by rw [eA']; exact dvd0
  have eR : 2 ^ 30 * R = A' := by rw [hR']; omega
  have R2 : R < 2 * p := by omega
  have hD'' : D' = if R < p then R else R - p := by
    rw [hD']; exact Nat.mod_eq_of_lt (by split <;> omega)
  refine ⟨by rw [hD'']; split <;> omega, ?_⟩
  have step1 : (2 ^ 30 * D' : Int) ≡ 2 ^ 30 * R [ZMOD p] := by
    rw [hD'']
    split
    · rfl
    · rename_i h
      have : ((R - p : Nat) : Int) = R - p := by omega
      rw [this]
      exact Int.modEq_iff_dvd.mpr ⟨2 ^ 30, by ring⟩
  refine step1.trans ?_
  have : (2 ^ 30 * R : Int) = A + q * p := by exact_mod_cast (eR.trans eA')
  rw [this]
  have e2 : ((A : Int) + q * p) ≡ A [ZMOD p] := Int.modEq_iff_dvd.mpr ⟨-q, by ring⟩
  refine e2.trans ?_
  have : (A : Int) = ((u.natAbs * T₁ : Nat) : Int) + ((v.natAbs * T₂ : Nat) : Int) := by
    rw [← Nat.cast_add]; exact_mod_cast (by omega : A = u.natAbs * T₁ + v.natAbs * T₂)
  rw [this]
  exact c1.add c2

/-- A small integer's word, as a signed number. -/
theorem small_toInt {c : Int} (h : |c| ≤ 2 ^ 30) : (BitVec.ofInt 32 c).toInt = c := by
  rw [abs_le] at h
  exact BitVec.toInt_ofInt_eq_self (by decide) (by omega) (by omega)

/-- A coefficient's word: its sign is its top bit, and its magnitude is its value's. -/
theorem small_sign {c : Int} (h : |c| ≤ 2 ^ 30) : (2 ^ 31 ≤ (BitVec.ofInt 32 c).toNat ↔ c < 0) := by
  have e := small_toInt h
  rw [BitVec.toInt_eq_toNat_cond] at e
  have := (BitVec.ofInt 32 c).isLt
  rw [abs_le] at h
  split at e <;> omega

theorem small_abs {c : Int} (h : |c| ≤ 2 ^ 30) : (BitVec.ofInt 32 c).toInt.natAbs = c.natAbs := by
  rw [small_toInt h]

/-! ## The end -/

/-- `f` from its words modulo `M = 2^32 P`, `|f| < P`: its sign is the top half of `M`, and its
magnitude the low part of its words or of their negation. -/
theorem abs_words {P F T : Nat} {f : Int} (hP : 0 < P) (hF : F < 2 ^ 32 * P)
    (hFf : (F : Int) % ((2 ^ 32 * P : Nat) : Int) = f % ((2 ^ 32 * P : Nat) : Int)) (hf : f.natAbs < P) :
    (2 ^ 31 * P ≤ F ↔ f < 0) ∧ (¬ f < 0 → F % P = f.natAbs) ∧
      (f < 0 → ∀ b, T + F = 0 + 2 ^ 32 * P * b → T < 2 ^ 32 * P → T % P = f.natAbs) := by
  have hM : (0 : Int) < ((2 ^ 32 * P : Nat) : Int) := by exact_mod_cast Nat.mul_pos (by decide) hP
  have h2 : 2 * P ≤ 2 ^ 31 * P := Nat.mul_le_mul_right _ (by decide)
  have hPM : (2 ^ 32 * P : Nat) = 2 * (2 ^ 31 * P) := by rw [← Nat.mul_assoc]; rfl
  by_cases hneg : f < 0
  · have eF : (F : Int) = f + ((2 ^ 32 * P : Nat) : Int) := by
      have := Int.emod_emod_of_dvd f (dvd_refl ((2 ^ 32 * P : Nat) : Int))
      have e1 : (F : Int) % ((2 ^ 32 * P : Nat) : Int) = F := Int.emod_eq_of_lt (by omega) (by exact_mod_cast hF)
      have e2 : f % ((2 ^ 32 * P : Nat) : Int) = f + ((2 ^ 32 * P : Nat) : Int) := by
        rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]
      rw [← e1, hFf, e2]
    refine ⟨⟨fun _ => hneg, fun _ => by omega⟩, fun h => absurd hneg h, fun _ b hb hT => ?_⟩
    have hb1 : b = 1 := by
      rcases Nat.lt_or_ge b 2 with h | h
      · rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
        · omega
        · rfl
      · have : 2 ^ 32 * P * 2 ≤ 2 ^ 32 * P * b := Nat.mul_le_mul_left _ h
        omega
    subst hb1
    have : (T : Int) = -f := by omega
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  · have eF : (F : Int) = f := by
      have e1 : (F : Int) % ((2 ^ 32 * P : Nat) : Int) = F := Int.emod_eq_of_lt (by omega) (by exact_mod_cast hF)
      rw [← e1, hFf, Int.emod_eq_of_lt (by omega) (by omega)]
    refine ⟨⟨fun h => by omega, fun h => absurd h hneg⟩, fun _ => ?_, fun h => absurd h hneg⟩
    rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- `±d mod p` from its two selections. -/
theorem sel_mod {p P M D T X : Nat} {sg : Prop} [Decidable sg] (hD : D < p) (hpP : p ≤ P)
    (hb : ∀ b, T + D = p + M * b → T = p - D) (hTD : ∃ b, T + D = p + M * b)
    (hX : X = (if (if sg then T else D) < p then (if sg then T else D) else (if sg then T else D) - p) % P) :
    X < p ∧ (X : Int) ≡ (if sg then -(D : Int) else D) [ZMOD p] := by
  obtain ⟨b, hb'⟩ := hTD
  have eT := hb b hb'
  by_cases h : sg
  · simp only [h, ↓reduceIte] at hX ⊢
    rw [eT] at hX
    by_cases h0 : D = 0
    · subst h0
      simp only [Nat.sub_zero, Nat.lt_irrefl, ↓reduceIte, Nat.sub_self, Nat.zero_mod] at hX
      subst hX
      exact ⟨by omega, by simp [Int.ModEq]⟩
    · have : p - D < p := by omega
      simp only [this, ↓reduceIte] at hX
      rw [Nat.mod_eq_of_lt (by omega)] at hX
      subst hX
      refine ⟨by omega, Int.modEq_iff_dvd.mpr ⟨-1, ?_⟩⟩
      push_cast [Nat.cast_sub (by omega : D ≤ p)]; ring
  · simp only [h, ↓reduceIte, hD] at hX ⊢
    rw [Nat.mod_eq_of_lt (by omega)] at hX
    subst hX; exact ⟨hD, rfl⟩


/-! ## The coefficients as functions of the inputs

`red30 p t` is `t / 2^30` modulo the odd `p`, as `t ((p + 1) / 2)^30 mod p`: the unique
`D < p` with `2^30 D ≡ t` (`red30_unique`). `deRun p x i` is the pair `(d, e)` after `i` batches
from `(0, 1)`, so a run's coefficients are a function of `p` and `x` alone. -/

theorem red30_spec {p : Nat} (hp : p % 2 = 1) (t : Int) :
    red30 p t < p ∧ (2 ^ 30 * red30 p t : Int) ≡ t [ZMOD p] := by
  have hp0 : (0 : Int) < p := Int.natCast_pos.mpr (by omega)
  have nn := Int.emod_nonneg (t * (((p + 1) / 2 : Nat) : Int) ^ 30) hp0.ne'
  have lt := Int.emod_lt_of_pos (t * (((p + 1) / 2 : Nat) : Int) ^ 30) hp0
  have e : ((red30 p t : Nat) : Int) = t * (((p + 1) / 2 : Nat) : Int) ^ 30 % p := by
    unfold red30; exact Int.toNat_of_nonneg nn
  refine ⟨by omega, ?_⟩
  rw [e]
  have h2 : (2 : Int) * (((p + 1) / 2 : Nat) : Int) = p + 1 := by
    have : 2 * ((p + 1) / 2) = p + 1 := by omega
    exact_mod_cast this
  have one : ((p : Int) + 1) ^ 30 ≡ 1 [ZMOD p] := by
    have : (p : Int) + 1 ≡ 1 [ZMOD p] := by simp [Int.ModEq]
    simpa using this.pow 30
  calc 2 ^ 30 * (t * (((p + 1) / 2 : Nat) : Int) ^ 30 % p)
      ≡ 2 ^ 30 * (t * (((p + 1) / 2 : Nat) : Int) ^ 30) [ZMOD p] := (Int.mod_modEq _ _).mul_left _
    _ = t * ((p : Int) + 1) ^ 30 := by rw [← h2, mul_pow]; ring
    _ ≡ t * 1 [ZMOD p] := one.mul_left _
    _ = t := mul_one t

theorem red30_unique {p D : Nat} {t : Int} (hp : p % 2 = 1) (hD : D < p)
    (h : (2 ^ 30 * D : Int) ≡ t [ZMOD p]) : D = red30 p t := by
  have hp0 : (0 : Int) < p := Int.natCast_pos.mpr (by omega)
  obtain ⟨r1, r2⟩ := red30_spec hp t
  have c := cancel_pow2 (N := 30) (by exact_mod_cast hp) hp0 (h.trans r2.symm)
  have := Int.emod_emod_of_dvd (D : Int) (dvd_refl (p : Int))
  rw [Int.ModEq, Int.emod_eq_of_lt (by omega) (by exact_mod_cast hD),
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast r1)] at c
  exact_mod_cast c

/-- `d`, `f` and `g` do not depend on `invRun`'s `m`. -/
theorem invRun_dfg_m {p m m' x : Int} (hp : p % 2 = 1) (i : Nat) :
    (invRun 30 p m x i).d = (invRun 30 p m' x i).d ∧ (invRun 30 p m x i).f = (invRun 30 p m' x i).f ∧
      (invRun 30 p m x i).g = (invRun 30 p m' x i).g := by
  have h := (invRun_dfg (N := 30) (m := m) (x := x) hp i).1
  have h' := (invRun_dfg (N := 30) (m := m') (x := x) hp i).1
  rw [← h'] at h
  simp only [Prod.mk.injEq] at h
  exact h

theorem deStep_m {p : Nat} {m : Int} (hp : p % 2 = 1) (x i : Nat) (de : Nat × Nat) :
    deStep p (invRun 30 p m x i) de = deStep p (invRun 30 p 0 x i) de := by
  obtain ⟨d, f, g⟩ := invRun_dfg_m (p := (p : Int)) (m := m) (m' := 0) (x := x) (by exact_mod_cast hp) i
  unfold deStep; rw [d, f, g]

/-- With `f ≡ x d` and `g ≡ x e` modulo `p` throughout. -/
theorem deRun_cong {p x : Nat} (hp : p % 2 = 1) (hp1 : 1 < p) : ∀ i,
    (invRun 30 p 0 x i).f ≡ x * (deRun p x i).1 [ZMOD p] ∧
      (invRun 30 p 0 x i).g ≡ x * (deRun p x i).2 [ZMOD p] ∧ (deRun p x i).1 < p ∧ (deRun p x i).2 < p
  | 0 => by
    refine ⟨?_, ?_, by simp only [deRun]; omega, by simp only [deRun]; exact hp1⟩
    · simp [invRun, deRun, Int.ModEq]
    · simp [invRun, deRun]
  | i + 1 => by
    obtain ⟨hF, hG, -, -⟩ := deRun_cong hp hp1 i
    have hpI : (p : Int) % 2 = 1 := by exact_mod_cast hp
    have hodd := (invRun_dfg (N := 30) (m := 0) (x := (x : Int)) hpI i).2
    obtain ⟨a1, a2⟩ := red30_spec hp ((msteps 30 (MSt.init (invRun 30 p 0 x i).d (invRun 30 p 0 x i).f
      (invRun 30 p 0 x i).g)).u * (deRun p x i).1 + (msteps 30 (MSt.init (invRun 30 p 0 x i).d
      (invRun 30 p 0 x i).f (invRun 30 p 0 x i).g)).v * (deRun p x i).2)
    obtain ⟨b1, b2⟩ := red30_spec hp ((msteps 30 (MSt.init (invRun 30 p 0 x i).d (invRun 30 p 0 x i).f
      (invRun 30 p 0 x i).g)).q * (deRun p x i).1 + (msteps 30 (MSt.init (invRun 30 p 0 x i).d
      (invRun 30 p 0 x i).f (invRun 30 p 0 x i).g)).r * (deRun p x i).2)
    have c := batch_cong30 (m := 0) hpI (by omega) hodd hF hG a2 b2
    simp only [invRun, deRun, deStep]
    exact ⟨c.1, c.2, a1, b1⟩

end VG.Proof.Divstep.W32
