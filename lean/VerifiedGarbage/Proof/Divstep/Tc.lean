import VerifiedGarbage.Proof.Divstep.Alg

/-!
# Inversion by batches of divsteps: words in two's complement

A signed number in `[-H, H)` is held in `[0, 2H)` as itself, or plus `2H`
if negative (`tc_eq`); the reduction `mred` on such words, as the code does
it (`mred_words`): sign-extend `t` by a word, add `k p`, take the words above
the lowest, add `p` if negative, subtract `p`, and add `p` back if negative.
-/

namespace VG.Proof.Divstep

/-- `W ≡ x (mod 2H)`, `W ∈ [0, 2H)`, `x ∈ [-H, H)`: `W` is `x`, or `x + 2H` if negative. -/
theorem tc_eq {H x W : Int} (hH : 0 < H) (hx1 : -H ≤ x) (hx2 : x < H) (hW0 : 0 ≤ W) (hW1 : W < 2 * H)
    (hc : W % (2 * H) = x % (2 * H)) : W = x + if x < 0 then 2 * H else 0 := by
  have hc'' : W ≡ x [ZMOD 2 * H] := hc
  obtain ⟨c, hc'⟩ := hc''.dvd
  have c1 : c ≤ 0 := by
    by_contra h; push Not at h
    have : 2 * H * 1 ≤ 2 * H * c := mul_le_mul_of_nonneg_left (by omega) (by omega)
    linarith
  have c2 : -1 ≤ c := by
    by_contra h; push Not at h
    have : 2 * H * c ≤ 2 * H * (-2) := mul_le_mul_of_nonneg_left (by omega) (by omega)
    linarith
  split
  · have : c = -1 := by
      by_contra h
      have : c = 0 := by omega
      subst this; linarith
    subst this; linarith
  · have : c = 0 := by
      by_contra h
      have : c = -1 := by omega
      subst this; linarith
    subst this; linarith

/-- The sign of such a word: its top half. -/
theorem tc_neg {H x W : Int} (hx1 : -H ≤ x) (hx2 : x < H)
    (h : W = x + if x < 0 then 2 * H else 0) : (H ≤ W ↔ x < 0) := by
  split at h <;> constructor <;> intro <;> omega

/-- `-p < mredRaw t < 2p` for `|t| ≤ 2^63 p`. -/
theorem mredRaw_range {p m t : Int} (hp : 0 < p) (hm : (p * m + 1) % 2 ^ 64 = 0) (ht : |t| ≤ 2 ^ 63 * p) :
    -p < mredRaw p m t ∧ mredRaw p m t < 2 * p := by
  have hraw := mredRaw_spec (t := t) hm
  have hk0 : 0 ≤ (t * m) % 2 ^ 64 := Int.emod_nonneg _ (by norm_num)
  have hk1 : (t * m) % 2 ^ 64 < 2 ^ 64 := Int.emod_lt_of_pos _ (by norm_num)
  rw [abs_le] at ht
  constructor
  · by_contra h; push Not at h
    have : 2 ^ 64 * mredRaw p m t ≤ 2 ^ 64 * (-p) := by nlinarith
    nlinarith
  · by_contra h; push Not at h
    have : 2 ^ 64 * (2 * p) ≤ 2 ^ 64 * mredRaw p m t := by nlinarith
    nlinarith

/-- `mred` as the code computes it, on words of `n + 1` (`A = 2^(64 n)`, `p < A`):
`W` holds `t`; `E` the sum `W + A 2^64 S + k p` modulo `A 2^128`, for `W`'s sign
word `S` and `k ≡ W m`; `R` its words above the lowest; `R₁ = R + p` if
negative; `R₂ = R₁ - p`; `R₃ = R₂ + p` if negative. -/
theorem mred_words {A B H p m t W k E R R₁ R₂ R₃ : Int} (hB : B = 2 ^ 64) (hH : H = 2 ^ 63) (hA : 0 < A)
    (hp : 0 < p) (hpA : p < A) (hm : (p * m + 1) % B = 0) (ht : |t| ≤ 2 ^ 63 * p)
    (hW0 : 0 ≤ W) (hW1 : W < A * B) (hWt : W % (A * B) = t % (A * B))
    (hk0 : 0 ≤ k) (hk1 : k < B) (hk : k % B = (W * m) % B)
    (hE : E = (W + A * B * (if A * H ≤ W then B - 1 else 0) + k * p) % (A * B * B))
    (hR : R = E / B)
    (hR₁ : R₁ = (R + if A * H ≤ R then p else 0) % (A * B))
    (hR₂0 : 0 ≤ R₂) (hR₂1 : R₂ < A * B) (hR₂ : (R₂ + p) % (A * B) = R₁)
    (hR₃ : R₃ = (R₂ + if A * H ≤ R₂ then p else 0) % (A * B)) :
    R₃ = mred p m t := by
  subst hB hH
  have hH : 0 < A * 2 ^ 63 := by positivity
  have hQ : A * 2 ^ 64 = 2 * (A * 2 ^ 63) := by ring
  have hpH : 2 * p < A * 2 ^ 63 := by nlinarith
  rw [abs_le] at ht
  have htH : -(A * 2 ^ 63) ≤ t ∧ t < A * 2 ^ 63 := by
    constructor <;> nlinarith
  -- `W` holds `t`.
  have eW := tc_eq hH htH.1 htH.2 hW0 (by rw [← hQ]; exact hW1) (by rw [← hQ]; exact hWt)
  have sW := tc_neg htH.1 htH.2 eW
  -- `k = t m mod 2^64`.
  have hk' : k = (t * m) % 2 ^ 64 := by
    have h64 : (2 : Int) ^ 64 ∣ A * 2 ^ 64 := dvd_mul_left _ _
    have hWt' : W % 2 ^ 64 = t % 2 ^ 64 := by
      rw [← Int.emod_emod_of_dvd W h64, ← Int.emod_emod_of_dvd t h64, hWt]
    rw [← Int.emod_eq_of_lt hk0 hk1, hk, Int.mul_emod, hWt', ← Int.mul_emod]
  -- The sum is `t + k p = 2^64 r`, in two's complement.
  set r := mredRaw p m t with hr
  have hraw : 2 ^ 64 * r = t + (t * m) % 2 ^ 64 * p := mredRaw_spec hm
  rw [← hk'] at hraw
  obtain ⟨rlo, rhi⟩ := mredRaw_range hp hm (abs_le.mpr ⟨by linarith, ht.2⟩)
  rw [← hr] at rlo rhi
  have hE' : E = 2 ^ 64 * (r + if r < 0 then A * 2 ^ 64 else 0) := by
    have hX : W + A * 2 ^ 64 * (if A * 2 ^ 63 ≤ W then 2 ^ 64 - 1 else 0) + k * p =
        2 ^ 64 * r + (if r < 0 then A * 2 ^ 64 * 2 ^ 64 else 0) + A * 2 ^ 64 * 2 ^ 64 *
          ((if t < 0 then 1 else 0) - (if r < 0 then 1 else 0)) := by
      have hS : (if A * 2 ^ 63 ≤ W then (2 : Int) ^ 64 - 1 else 0) = if t < 0 then 2 ^ 64 - 1 else 0 := by
        simp only [sW]
      have hkp : k * p = 2 ^ 64 * r - t := by linarith
      rw [hS, eW, hkp]
      by_cases h1 : t < 0 <;> by_cases h2 : r < 0 <;> simp only [h1, h2, ↓reduceIte] <;> ring
    rw [hE, hX, Int.add_mul_emod_self_left]
    have h0 : 0 ≤ 2 ^ 64 * r + (if r < 0 then A * 2 ^ 64 * 2 ^ 64 else 0) := by
      split <;> nlinarith
    have h1 : 2 ^ 64 * r + (if r < 0 then A * 2 ^ 64 * 2 ^ 64 else 0) < A * 2 ^ 64 * 2 ^ 64 := by
      split <;> nlinarith
    rw [Int.emod_eq_of_lt h0 h1]
    split <;> ring
  have eR : R = r + if r < 0 then 2 * (A * 2 ^ 63) else 0 := by
    rw [hR, hE', Int.mul_ediv_cancel_left _ (by norm_num), hQ]
  have rH : -(A * 2 ^ 63) ≤ r ∧ r < A * 2 ^ 63 := ⟨by linarith, by linarith⟩
  have sR := tc_neg rH.1 rH.2 eR
  -- `R₁ = r + p` if negative, else `r`.
  have eR₁ : R₁ = r + if r < 0 then p else 0 := by
    have hc : (if A * 2 ^ 63 ≤ R then p else 0) = if r < 0 then p else 0 := by simp only [sR]
    rw [hR₁, hc, eR, hQ]
    by_cases h : r < 0
    · simp only [h, ↓reduceIte]
      rw [show r + 2 * (A * 2 ^ 63) + p = r + p + 2 * (A * 2 ^ 63) * 1 by ring, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt (by linarith) (by linarith)]
    · simp only [h, ↓reduceIte, Int.add_zero]
      rw [Int.emod_eq_of_lt (by linarith) (by linarith)]
  -- `R₂ = R₁ - p`, in two's complement.
  obtain ⟨r₂, hr₂⟩ : ∃ r₂, r₂ = r + (if r < 0 then p else 0) - p := ⟨_, rfl⟩
  have r₂lo : -p ≤ r₂ := by rw [hr₂]; split <;> linarith
  have r₂hi : r₂ < p := by rw [hr₂]; split <;> linarith
  have eR₂ : R₂ = r₂ + if r₂ < 0 then 2 * (A * 2 ^ 63) else 0 := by
    refine tc_eq hH (by linarith) (by linarith) hR₂0 (by rw [← hQ]; exact hR₂1) ?_
    have h1 : (R₂ + p) % (A * 2 ^ 64) = (r₂ + p) % (A * 2 ^ 64) := by
      rw [hR₂, eR₁, Int.emod_eq_of_lt (a := r₂ + p) (by linarith) (by linarith), hr₂]; ring
    rw [← hQ]; exact Int.ModEq.add_right_cancel' p h1
  have sR₂ := tc_neg (by linarith) (by linarith) eR₂
  -- `R₃ = norm p r`.
  have hc₂ : (if A * 2 ^ 63 ≤ R₂ then p else 0) = if r₂ < 0 then p else 0 := by simp only [sR₂]
  rw [hR₃, hc₂, eR₂, hQ]
  unfold mred norm
  rw [← hr]
  by_cases h2 : r₂ < 0
  · simp only [h2, ↓reduceIte]
    rw [show r₂ + 2 * (A * 2 ^ 63) + p = r₂ + p + 2 * (A * 2 ^ 63) * 1 by ring, Int.add_mul_emod_self_left,
      Int.emod_eq_of_lt (by linarith) (by linarith), hr₂]
    by_cases h : r < 0
    · simp only [h, ↓reduceIte]; ring
    · have h' : ¬ p ≤ r := by rw [hr₂] at h2; simp only [h, ↓reduceIte] at h2; linarith
      simp only [h, h', ↓reduceIte]; ring
  · simp only [h2, ↓reduceIte, Int.add_zero]
    rw [Int.emod_eq_of_lt (by linarith) (by linarith), hr₂]
    by_cases h : r < 0
    · rw [hr₂] at h2; simp only [h, ↓reduceIte] at h2; linarith
    · have h' : p ≤ r := by rw [hr₂] at h2; simp only [h, ↓reduceIte] at h2; linarith
      simp only [h, h', ↓reduceIte]; ring

/-- `mred_words` on natural numbers, as words hold them. -/
theorem ite_natCast_le {a b : Nat} {x y : Int} : (if (a : Int) ≤ b then x else y) = if a ≤ b then x else y := by
  by_cases h : a ≤ b
  · simp only [h, Int.ofNat_le.mpr h, ↓reduceIte]
  · have h' : ¬ (a : Int) ≤ b := fun h' => h (Int.ofNat_le.mp h')
    simp only [h, h', ↓reduceIte]

/-- `mred_words` on natural numbers, as words hold them (`B = 2^64`, `H = 2^63`). -/
theorem mred_nat {A B H p m W k E R R₁ R₂ R₃ : Nat} {t : Int} (hB : B = 2 ^ 64) (hH : H = 2 ^ 63) (hA : 0 < A)
    (hp : 0 < p) (hpA : p < A) (hm : (p * m + 1) % B = 0) (ht : |t| ≤ 2 ^ 63 * p)
    (hW1 : W < A * B) (hWt : (W : Int) % ((A * B : Nat) : Int) = t % ((A * B : Nat) : Int))
    (hk : k = W % B * m % B)
    (hE : E = (W + A * B * (if A * H ≤ W then B - 1 else 0) + k * p) % (A * B * B))
    (hR : R = E / B)
    (hR₁ : R₁ = (R + if A * H ≤ R then p else 0) % (A * B))
    (hR₂1 : R₂ < A * B) (hR₂ : (R₂ + p) % (A * B) = R₁)
    (hR₃ : R₃ = (R₂ + if A * H ≤ R₂ then p else 0) % (A * B)) :
    (R₃ : Int) = mred p m t := by
  have hB1 : 1 ≤ B := by rw [hB]; exact Nat.one_le_two_pow
  have hk1 : k < B := by rw [hk]; exact Nat.mod_lt _ (by omega)
  refine mred_words (A := A) (B := B) (H := H) (p := p) (m := m) (t := t) (W := W) (k := k) (E := E) (R := R)
    (R₁ := R₁) (R₂ := R₂) (R₃ := R₃) (by rw [hB]; norm_num) (by rw [hH]; norm_num) (by exact_mod_cast hA)
    (by exact_mod_cast hp) (by exact_mod_cast hpA) (by exact_mod_cast hm) ht (by omega) (by exact_mod_cast hW1)
    (by exact_mod_cast hWt) (by omega) (by exact_mod_cast hk1) ?_ ?_ ?_ ?_ (by omega) (by exact_mod_cast hR₂1) ?_ ?_
  · rw [hk]
    have h1 : W % B * m % B = W * m % B := by rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    rw [h1]; push_cast; rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
  · rw [hE, ← Nat.cast_mul A H, ite_natCast_le]; push_cast [Nat.cast_sub hB1]; rfl
  · rw [hR]; push_cast; rfl
  · rw [hR₁, ← Nat.cast_mul A H, ite_natCast_le]; push_cast; rfl
  · rw [← hR₂]; push_cast; rfl
  · rw [hR₃, ← Nat.cast_mul A H, ite_natCast_le]; push_cast; rfl

/-- A divstep keeps `|f|, |g| ≤ M` (from an odd `f`). -/
theorem divstep_le {M : Int} {t : Int × Int × Int} (hf : t.2.1 % 2 = 1) (h1 : |t.2.1| ≤ M) (h2 : |t.2.2| ≤ M) :
    |(divstep t).2.1| ≤ M ∧ |(divstep t).2.2| ≤ M := by
  obtain ⟨d, f, g⟩ := t
  simp only at hf h1 h2
  rw [abs_le] at h1 h2
  unfold divstep
  split
  · rename_i h
    simp only at h ⊢
    refine ⟨abs_le.mpr h2, abs_le.mpr ⟨?_, ?_⟩⟩ <;> omega
  · simp only
    refine ⟨abs_le.mpr h1, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
    · rcases Int.emod_two_eq_zero_or_one g with hg | hg <;> rw [hg] <;> omega

theorem divsteps_le {M d f g : Int} (hd : d % 2 = 1) (hf : f % 2 = 1) (h1 : |f| ≤ M) (h2 : |g| ≤ M) :
    ∀ n, |(divsteps n (d, f, g)).2.1| ≤ M ∧ |(divsteps n (d, f, g)).2.2| ≤ M
  | 0 => ⟨h1, h2⟩
  | n + 1 => by
    obtain ⟨a, b⟩ := divsteps_le hd hf h1 h2 n
    rw [divsteps_succ]
    exact divstep_le (divsteps_odd hd hf n).2 a b

/-- The arithmetic shift by 59 of `y = 2^59 z` held in `[0, 2H)` (two's complement), its
sign word appended: `z`, modulo `2H`. -/
theorem shr_words {H V y z D c B : Int} (hc : c = 2 ^ 59) (hB : B = 2 ^ 64) (hH : 0 < H) (hV0 : 0 ≤ V)
    (hV1 : V < 2 * H) (hVy : V % (2 * H) = y % (2 * H)) (hy1 : -H ≤ y) (hy2 : y < H) (hz : y = c * z)
    (hD : D = ((V + 2 * H * (if H ≤ V then B - 1 else 0)) / c) % (2 * H)) :
    D % (2 * H) = z % (2 * H) := by
  subst hc hB
  have eV := tc_eq hH hy1 hy2 hV0 hV1 hVy
  have sV := tc_neg hy1 hy2 eV
  have e : V + 2 * H * (if H ≤ V then 2 ^ 64 - 1 else 0) = 2 ^ 59 * (z + (if y < 0 then 2 * H * 2 ^ 5 else 0)) := by
    have hc : (if H ≤ V then (2 : Int) ^ 64 - 1 else 0) = if y < 0 then 2 ^ 64 - 1 else 0 := by simp only [sV]
    rw [hc, eV, hz]
    split <;> ring
  rw [hD, e, Int.mul_ediv_cancel_left _ (by norm_num), Int.emod_emod_of_dvd _ (dvd_refl _)]
  split
  · rw [show z + 2 * H * 2 ^ 5 = z + 2 * H * 2 ^ 5 from rfl, Int.add_mul_emod_self_left]
  · rw [Int.add_zero]

/-- The masked linear combination: unsigned products less `2^64` times the
other factor where a word is negative is the signed combination, modulo `M`,
given `2^64 X' ≡ 2^64 X` (the factor's words but the top). -/
theorem lin_words {M V X X' Y Y' W W' : Int} {c c' : Prop} [Decidable c] [Decidable c']
    (hX : (2 ^ 64 * X') % M = (2 ^ 64 * X) % M) (hY : (2 ^ 64 * Y') % M = (2 ^ 64 * Y) % M)
    (h : (V + 2 ^ 64 * ((if c then X' else 0) + (if c' then Y' else 0))) % M = (W * X + W' * Y) % M) :
    V % M = ((W - if c then 2 ^ 64 else 0) * X + (W' - if c' then 2 ^ 64 else 0) * Y) % M := by
  have h1 : V ≡ W * X + W' * Y - 2 ^ 64 * ((if c then X' else 0) + (if c' then Y' else 0)) [ZMOD M] := by
    have := Int.ModEq.sub_right (2 ^ 64 * ((if c then X' else 0) + (if c' then Y' else 0))) h
    simpa using this
  have h2 : 2 ^ 64 * ((if c then X' else 0) + (if c' then Y' else 0)) ≡
      2 ^ 64 * ((if c then X else 0) + (if c' then Y else 0)) [ZMOD M] := by
    have hX' : 2 ^ 64 * X' ≡ 2 ^ 64 * X [ZMOD M] := hX
    have hY' : 2 ^ 64 * Y' ≡ 2 ^ 64 * Y [ZMOD M] := hY
    split_ifs <;> simp only [mul_add, mul_zero, add_zero, zero_add]
    · exact hX'.add hY'
    · exact hX'
    · exact hY'
    · rfl
  have h3 := h1.trans (Int.ModEq.sub_left _ h2)
  rw [h3]
  congr 1
  split_ifs <;> ring

/-- A word as a signed number. -/
theorem toInt_sgn (w : BitVec 64) : (w.toNat : Int) - (if 2 ^ 63 ≤ w.toNat then 2 ^ 64 else 0) = w.toInt := by
  rw [BitVec.toInt_eq_toNat_cond]
  have := w.isLt
  split_ifs <;> push_cast <;> omega

/-- `shr_words` on natural numbers, as words hold them (`c = 2^59`, `B = 2^64`). -/
theorem shr_nat {H V D c B : Nat} {y z : Int} (hc : 2 ^ 59 = c) (hB : 2 ^ 64 = B) (hH : 0 < H) (hV1 : V < 2 * H)
    (hVy : (V : Int) % ((2 * H : Nat) : Int) = y % ((2 * H : Nat) : Int)) (hy1 : -(H : Int) ≤ y) (hy2 : y < H)
    (hz : y = 2 ^ 59 * z) (hD : D = (V + 2 * H * (if H ≤ V then B - 1 else 0)) / c % (2 * H)) :
    (D : Int) % ((2 * H : Nat) : Int) = z % ((2 * H : Nat) : Int) := by
  have hB1 : 1 ≤ B := by rw [← hB]; exact Nat.one_le_two_pow
  have hc' : (c : Int) = 2 ^ 59 := by rw [← hc]; norm_num
  have hB' : (B : Int) = 2 ^ 64 := by rw [← hB]; norm_num
  have hz' : y = (c : Int) * z := by rw [hc']; exact hz
  have hD' := congrArg (Nat.cast : Nat → Int) hD
  push_cast [Nat.cast_sub hB1] at hD' hVy ⊢
  rw [← ite_natCast_le] at hD'
  exact shr_words hc' hB' (by exact_mod_cast hH) (by omega) (by exact_mod_cast hV1) hVy hy1 hy2 hz' hD'

/-- A small integer's word, as a signed number. -/
theorem toInt_small {u : Int} (h : |u| ≤ 2 ^ 59) : (BitVec.ofInt 64 u).toInt = u := by
  rw [abs_le] at h
  exact BitVec.toInt_ofInt_eq_self (by decide) (by norm_num; omega) (by norm_num; omega)

/-- The combination of congruent numbers. -/
theorem cong_comb {Q u v X Y f g : Int} (hX : X % Q = f % Q) (hY : Y % Q = g % Q) :
    (u * X + v * Y) % Q = (u * f + v * g) % Q :=
  Int.ModEq.add (Int.ModEq.mul_left u hX) (Int.ModEq.mul_left v hY)

/-- A batch's combination of numbers at most `p`. -/
theorem comb_le {u v f g p : Int} (huv : |u| + |v| ≤ 2 ^ 59) (hf : |f| ≤ p) (hg : |g| ≤ p) :
    |u * f + v * g| ≤ 2 ^ 59 * p := by
  have hp : 0 ≤ p := le_trans (abs_nonneg _) hf
  calc |u * f + v * g| ≤ |u| * |f| + |v| * |g| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |u| * p + |v| * p := add_le_add (mul_le_mul_of_nonneg_left hf (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hg (abs_nonneg _))
    _ = (|u| + |v|) * p := by ring
    _ ≤ 2 ^ 59 * p := mul_le_mul_of_nonneg_right huv hp

/-- Within the half range of `L` words, for `p < 2^(64 (L - 1))`. -/
theorem comb_range {u v f g : Int} {p A : Nat} (huv : |u| + |v| ≤ 2 ^ 59) (hf : |f| ≤ p) (hg : |g| ≤ p)
    (hpA : p < A) : -((A * 2 ^ 63 : Nat) : Int) ≤ u * f + v * g ∧ u * f + v * g < ((A * 2 ^ 63 : Nat) : Int) := by
  have h := comb_le huv hf hg
  rw [abs_le] at h
  have hpA' : (p : Int) < A := by exact_mod_cast hpA
  have hp0 : (0 : Int) ≤ p := Int.natCast_nonneg _
  push_cast
  constructor <;> nlinarith

/-! ## Bounds over a run -/

theorem divstep_d (t : Int × Int × Int) : |(divstep t).1| ≤ |t.1| + 2 := by
  unfold divstep
  split <;> simp only <;> rw [abs_le] <;> constructor <;>
    linarith [abs_nonneg t.1, le_abs_self t.1, neg_abs_le t.1]

theorem divsteps_d (t : Int × Int × Int) : ∀ n, |(divsteps n t).1| ≤ |t.1| + 2 * n
  | 0 => by simp [divsteps]
  | n + 1 => by
    rw [divsteps_succ]
    have := divstep_d (divsteps n t)
    have := divsteps_d t n
    push_cast; linarith

/-- The state after `B` batches is bounded: `|d| ≤ 1 + 2 N B`, `f` odd, `|f|, |g| ≤ p`,
`a`, `b` in `[0, p)`. -/
theorem invRun_bounds {N : Nat} (hN : N ≤ 62) {p m x : Int} (hp : p % 2 = 1) (hp1 : 1 < p)
    (hm : (p * m + 1) % 2 ^ 64 = 0) (hx0 : 0 ≤ x) (hxp : x < p) (B : Nat) :
    |(invRun N p m x B).d| ≤ 1 + 2 * (N * B : Nat) ∧ (invRun N p m x B).f % 2 = 1 ∧
      |(invRun N p m x B).f| ≤ p ∧ |(invRun N p m x B).g| ≤ p ∧
      0 ≤ (invRun N p m x B).a ∧ (invRun N p m x B).a < p ∧ 0 ≤ (invRun N p m x B).b ∧ (invRun N p m x B).b < p := by
  obtain ⟨hd, hodd⟩ := invRun_dfg (N := N) (m := m) (x := x) hp B
  obtain ⟨-, -, a0, a1, b0, b1⟩ := invRun_inv (x := x) hN hp hp1 hm B
  have e1 : (invRun N p m x B).d = (divsteps (N * B) (1, p, x)).1 := by rw [← hd]
  have e2 : (invRun N p m x B).f = (divsteps (N * B) (1, p, x)).2.1 := by rw [← hd]
  have e3 : (invRun N p m x B).g = (divsteps (N * B) (1, p, x)).2.2 := by rw [← hd]
  obtain ⟨lf, lg⟩ := divsteps_le (M := p) (d := 1) (f := p) (g := x) (by decide) hp
    (by rw [abs_of_pos (by omega)]) (by rw [abs_of_nonneg hx0]; omega) (N * B)
  have ld := divsteps_d (1, p, x) (N * B)
  refine ⟨?_, hodd, by rw [e2]; exact lf, by rw [e3]; exact lg, a0, a1, b0, b1⟩
  rw [e1]; simpa using ld

/-- `n` steps from `g = 0`: `g` stays `0`, `u`, `v` double. -/
theorem msteps_g0 : ∀ (n : Nat) (d f u v q r : Int),
    msteps n ⟨d, f, 0, u, v, q, r⟩ = ⟨d + 2 * n, f, 0, 2 ^ n * u, 2 ^ n * v, q, r⟩
  | 0, d, f, u, v, q, r => by simp [msteps]
  | n + 1, d, f, u, v, q, r => by
    rw [msteps]
    have : mstep ⟨d, f, 0, u, v, q, r⟩ = ⟨2 + d, f, 0, 2 * u, 2 * v, q, r⟩ := by
      simp [mstep]
    rw [this, msteps_g0 n]
    simp only [MSt.mk.injEq]
    refine ⟨by push_cast; ring, trivial, trivial, by ring, by ring, trivial, trivial⟩

/-- From `x = 0`, `g` and `a` stay `0`. -/
theorem invRun_zero {N : Nat} {p m : Int} (hp : 0 < p) :
    ∀ B, (invRun N p m 0 B).g = 0 ∧ (invRun N p m 0 B).a = 0
  | 0 => ⟨rfl, rfl⟩
  | B + 1 => by
    obtain ⟨hg, ha⟩ := invRun_zero hp B
    simp only [invRun, batch]
    generalize invRun N p m 0 B = s at hg ha
    obtain ⟨d, f, g, a, b⟩ := s
    simp only at hg ha
    subst hg ha
    rw [MSt.init, msteps_g0]
    simp only [mul_zero, add_zero, zero_add, mul_one]
    simp [mred, mredRaw, norm, show ¬ p ≤ 0 by omega]

/-- Enough divsteps for numbers of `n` words: `590` for `n ≤ 4` (256 bits),
`885` for `n ≤ 6` (384). -/
theorem divsteps_words {f g : Int} {n N : Nat} (hf : f % 2 = 1) (hg : 0 ≤ g) (hgf : g ≤ f)
    (hfn : f < 2 ^ (64 * n)) (hb : (n ≤ 4 ∧ 590 ≤ N) ∨ (n ≤ 6 ∧ 885 ≤ N)) :
    (divsteps N (1, f, g)).2.2 = 0 ∧ (divsteps N (1, f, g)).2.1.natAbs = Int.gcd f g := by
  rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine divsteps_590 hf hg hgf ?_ h2
    calc f ≤ 2 ^ (64 * n) := hfn.le
      _ ≤ 2 ^ 256 := pow_le_pow_right₀ (by norm_num) (by omega)
  · refine divsteps_885 hf hg hgf ?_ h2
    calc f ≤ 2 ^ (64 * n) := hfn.le
      _ ≤ 2 ^ 384 := pow_le_pow_right₀ (by norm_num) (by omega)

end VG.Proof.Divstep
