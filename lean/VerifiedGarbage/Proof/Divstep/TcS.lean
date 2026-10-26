module
public import VerifiedGarbage.Proof.Divstep.Alg

import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Divstep.Batch
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Inversion by batches of divsteps: signed coefficients

`invRunS` is `invRun` with `(a, b)` left as `mredRaw` gives them, in
`(-p, 2p)` (`invRunS_range`), rather than brought into `[0, p)` at every
batch: its `d`, `f`, `g` are `invRun`'s and its `a`, `b` congruent to them
(`invRunS_rel`), so `norm p` of its `a` is `invRun`'s (`norm_invRunS`).
On words in two's complement (`tc_eq`), `mred_words` splits into the
reduction (`mredRaw_words`) and the normalization (`norm_words`).
-/

@[expose] public section

namespace VG.Proof.Divstep

/-- A batch of `N` divsteps, `(a, b)` by `mredRaw`. -/
def batchS (N : Nat) (p m : Int) (s : IState) : IState :=
  let t := msteps N (MSt.init s.d s.f s.g)
  ⟨t.d, (t.u * s.f + t.v * s.g) / 2 ^ N, (t.q * s.f + t.r * s.g) / 2 ^ N,
    mredRaw p m (t.u * s.a + t.v * s.b), mredRaw p m (t.q * s.a + t.r * s.b)⟩

/-- `B` such batches from the start. -/
def invRunS (N : Nat) (p m x : Int) : Nat → IState
  | 0 => ⟨1, p, x, 0, 1⟩
  | B + 1 => batchS N p m (invRunS N p m x B)

/-- `mredRaw` of congruent numbers are congruent. -/
theorem mredRaw_cong {p m t t' : Int} (hp : p % 2 = 1) (hp0 : 0 < p) (hm : (p * m + 1) % 2 ^ 64 = 0)
    (h : t ≡ t' [ZMOD p]) : mredRaw p m t ≡ mredRaw p m t' [ZMOD p] := by
  apply cancel_pow2 (N := 64) hp hp0
  have e : ∀ t, 2 ^ 64 * mredRaw p m t ≡ t [ZMOD p] := fun t => by
    rw [mredRaw_spec hm]; exact Int.add_mul_emod_self_right _ _ _
  exact ((e t).trans h).trans (e t').symm

/-- `mredRaw` is `mred` modulo `p`. -/
theorem mredRaw_cong_mred {p m t : Int} : mredRaw p m t ≡ mred p m t [ZMOD p] := by
  unfold mred norm
  split
  · exact Int.modEq_iff_dvd.mpr ⟨1, by ring⟩
  · split
    · exact Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩
    · exact Int.ModEq.refl _

/-- `invRunS` is `invRun` but for `a`, `b`, which are congruent. -/
theorem invRunS_rel {N : Nat} {p m x : Int} (hp : p % 2 = 1) (hp0 : 0 < p) (hm : (p * m + 1) % 2 ^ 64 = 0) :
    ∀ B, (invRunS N p m x B).d = (invRun N p m x B).d ∧ (invRunS N p m x B).f = (invRun N p m x B).f ∧
      (invRunS N p m x B).g = (invRun N p m x B).g ∧
      (invRunS N p m x B).a ≡ (invRun N p m x B).a [ZMOD p] ∧ (invRunS N p m x B).b ≡ (invRun N p m x B).b [ZMOD p]
  | 0 => ⟨rfl, rfl, rfl, Int.ModEq.refl _, Int.ModEq.refl _⟩
  | B + 1 => by
    obtain ⟨hd, hf, hg, ha, hb⟩ := invRunS_rel (N := N) (x := x) hp hp0 hm B
    simp only [invRunS, invRun, batchS, batch]
    rw [hd, hf, hg]
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · exact (mredRaw_cong hp hp0 hm ((ha.mul_left _).add (hb.mul_left _))).trans mredRaw_cong_mred
    · exact (mredRaw_cong hp hp0 hm ((ha.mul_left _).add (hb.mul_left _))).trans mredRaw_cong_mred

/-- A combination by a matrix row of sum at most `2^N` of numbers below `2p` in magnitude. -/
theorem comb_le2 {N : Nat} (hN : N ≤ 62) {y z a b p : Int} (hp : 0 < p) (hyz : |y| + |z| ≤ 2 ^ N)
    (ha : |a| ≤ 2 * p) (hb : |b| ≤ 2 * p) : |y * a + z * b| ≤ 2 ^ 63 * p := by
  have h62 : (2 : Int) ^ N ≤ 2 ^ 62 := pow_le_pow_right₀ (by norm_num) hN
  calc |y * a + z * b| ≤ |y| * |a| + |z| * |b| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ |y| * (2 * p) + |z| * (2 * p) := add_le_add (mul_le_mul_of_nonneg_left ha (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hb (abs_nonneg _))
    _ = (|y| + |z|) * (2 * p) := by ring
    _ ≤ 2 ^ 62 * (2 * p) := mul_le_mul_of_nonneg_right (le_trans hyz h62) (by omega_arith)
    _ = 2 ^ 63 * p := by ring

/-- `a`, `b` stay in `(-p, 2p)`. -/
theorem invRunS_range {N : Nat} (hN : N ≤ 62) {p m x : Int} (hp1 : 1 < p) (hm : (p * m + 1) % 2 ^ 64 = 0) :
    ∀ B, -p < (invRunS N p m x B).a ∧ (invRunS N p m x B).a < 2 * p ∧
      -p < (invRunS N p m x B).b ∧ (invRunS N p m x B).b < 2 * p
  | 0 => by simp only [invRunS]; omega_arith
  | B + 1 => by
    obtain ⟨a0, a1, b0, b1⟩ := invRunS_range (x := x) hN hp1 hm B
    set s := invRunS N p m x B
    obtain ⟨bu, bq⟩ := msteps_bnd s.d s.f s.g N
    have ha : |s.a| ≤ 2 * p := abs_le.mpr ⟨by omega_arith, by omega_arith⟩
    have hb : |s.b| ≤ 2 * p := abs_le.mpr ⟨by omega_arith, by omega_arith⟩
    have rA := mredRaw_range (by omega_arith) hm (comb_le2 hN (by omega_arith) bu ha hb)
    have rB := mredRaw_range (by omega_arith) hm (comb_le2 hN (by omega_arith) bq ha hb)
    simp only [invRunS, batchS]
    exact ⟨rA.1, rA.2, rB.1, rB.2⟩

/-- `norm p r ≡ r` modulo `p`. -/
theorem norm_cong {p r : Int} : norm p r ≡ r [ZMOD p] := by
  have := (mredRaw_cong_mred (p := p) (m := 0) (t := 2 ^ 64 * r)).symm
  unfold mred at this
  have e : mredRaw p 0 (2 ^ 64 * r) = r := by
    unfold mredRaw
    simp only [mul_zero, Int.zero_emod, zero_mul, add_zero]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  rwa [e] at this

/-- `norm p r` is in `[0, p)` for `r ∈ (-p, 2p)`. -/
theorem norm_range {p r : Int} (h0 : -p < r) (h1 : r < 2 * p) : 0 ≤ norm p r ∧ norm p r < p := by
  unfold norm
  split
  · omega_arith
  · split <;> omega_arith

/-- `norm p` of the signed run's `a` is the run's. -/
theorem norm_invRunS {N : Nat} (hN : N ≤ 62) {p m x : Int} (hp : p % 2 = 1) (hp1 : 1 < p)
    (hm : (p * m + 1) % 2 ^ 64 = 0) (B : Nat) : norm p (invRunS N p m x B).a = (invRun N p m x B).a := by
  obtain ⟨-, -, -, ha, -⟩ := invRunS_rel (N := N) (x := x) hp (by omega_arith) hm B
  obtain ⟨a0, a1, -, -⟩ := invRunS_range (x := x) hN hp1 hm B
  obtain ⟨-, -, c0, c1, -, -⟩ := invRun_inv (x := x) hN hp hp1 hm B
  obtain ⟨n0, n1⟩ := norm_range a0 a1
  have h : norm p (invRunS N p m x B).a ≡ (invRun N p m x B).a [ZMOD p] := norm_cong.trans ha
  rw [Int.ModEq, Int.emod_eq_of_lt n0 n1, Int.emod_eq_of_lt c0 c1] at h
  exact h

/-- `mredRaw` as the code computes it, on words of `n + 1` (`A = 2^(64 n)`, `p < A`):
`W` holds `t`; `E` the sum `W + A 2^64 S + k p` modulo `A 2^128`, for `W`'s sign
word `S` and `k ≡ W m`; `R` its words above the lowest, which hold `mredRaw p m t`. -/
theorem mredRaw_words {A B H p m t W k E R : Int} (hB : B = 2 ^ 64) (hH : H = 2 ^ 63) (hA : 0 < A)
    (hp : 0 < p) (hpA : p < A) (hm : (p * m + 1) % B = 0) (ht : |t| ≤ 2 ^ 63 * p)
    (hW0 : 0 ≤ W) (hW1 : W < A * B) (hWt : W % (A * B) = t % (A * B))
    (hk0 : 0 ≤ k) (hk1 : k < B) (hk : k % B = (W * m) % B)
    (hE : E = (W + A * B * (if A * H ≤ W then B - 1 else 0) + k * p) % (A * B * B))
    (hR : R = E / B) :
    R % (A * B) = mredRaw p m t % (A * B) := by
  subst hB hH
  have hH : 0 < A * 2 ^ 63 := by positivity
  have hQ : A * 2 ^ 64 = 2 * (A * 2 ^ 63) := by ring
  have hpH : 2 * p < A * 2 ^ 63 := by omega_arith
  rw [abs_le] at ht
  have htH : -(A * 2 ^ 63) ≤ t ∧ t < A * 2 ^ 63 := by
    constructor <;> omega_arith
  have eW := tc_eq hH htH.1 htH.2 hW0 (by rw [← hQ]; exact hW1) (by rw [← hQ]; exact hWt)
  have sW := tc_neg htH.1 htH.2 eW
  have hk' : k = (t * m) % 2 ^ 64 := by
    have h64 : (2 : Int) ^ 64 ∣ A * 2 ^ 64 := dvd_mul_left _ _
    have hWt' : W % 2 ^ 64 = t % 2 ^ 64 := by
      rw [← Int.emod_emod_of_dvd W h64, ← Int.emod_emod_of_dvd t h64, hWt]
    rw [← Int.emod_eq_of_lt hk0 hk1, hk, Int.mul_emod, hWt', ← Int.mul_emod]
  set r := mredRaw p m t with hr
  have hraw : 2 ^ 64 * r = t + (t * m) % 2 ^ 64 * p := mredRaw_spec hm
  rw [← hk'] at hraw
  obtain ⟨rlo, rhi⟩ := mredRaw_range hp hm (abs_le.mpr ⟨by omega_arith, ht.2⟩)
  rw [← hr] at rlo rhi
  have hE' : E = 2 ^ 64 * (r + if r < 0 then A * 2 ^ 64 else 0) := by
    have hX : W + A * 2 ^ 64 * (if A * 2 ^ 63 ≤ W then 2 ^ 64 - 1 else 0) + k * p =
        2 ^ 64 * r + (if r < 0 then A * 2 ^ 64 * 2 ^ 64 else 0) + A * 2 ^ 64 * 2 ^ 64 *
          ((if t < 0 then 1 else 0) - (if r < 0 then 1 else 0)) := by
      have hS : (if A * 2 ^ 63 ≤ W then (2 : Int) ^ 64 - 1 else 0) = if t < 0 then 2 ^ 64 - 1 else 0 := by
        simp only [sW]
      have hkp : k * p = 2 ^ 64 * r - t := by omega_arith
      rw [hS, eW, hkp]
      by_cases h1 : t < 0 <;> by_cases h2 : r < 0 <;> simp only [h1, h2, ↓reduceIte] <;> ring
    rw [hE, hX, Int.add_mul_emod_self_left]
    have h0 : 0 ≤ 2 ^ 64 * r + (if r < 0 then A * 2 ^ 64 * 2 ^ 64 else 0) := by
      split <;> omega_arith
    have h1 : 2 ^ 64 * r + (if r < 0 then A * 2 ^ 64 * 2 ^ 64 else 0) < A * 2 ^ 64 * 2 ^ 64 := by
      split <;> omega_arith
    rw [Int.emod_eq_of_lt h0 h1]
    split <;> ring
  rw [hR, hE', Int.mul_ediv_cancel_left _ (by norm_num)]
  split
  · exact Int.add_emod_right _ _
  · rw [add_zero]

/-- The normalization as the code computes it, on words of `n + 1` (`A = 2^(64 n)`,
`p < A`): `R` holds `r ∈ (-p, 2p)`; `R₁ = R + p` if negative; `R₂ = R₁ - p`;
`R₃ = R₂ + p` if negative, which is `norm p r`. -/
theorem norm_words {A B H p r R R₁ R₂ R₃ : Int} (hB : B = 2 ^ 64) (hH : H = 2 ^ 63) (hA : 0 < A)
    (hpA : p < A) (hr0 : -p < r) (hr1 : r < 2 * p)
    (hR0 : 0 ≤ R) (hR1 : R < A * B) (hRr : R % (A * B) = r % (A * B))
    (hR₁ : R₁ = (R + if A * H ≤ R then p else 0) % (A * B))
    (hR₂0 : 0 ≤ R₂) (hR₂1 : R₂ < A * B) (hR₂ : (R₂ + p) % (A * B) = R₁)
    (hR₃ : R₃ = (R₂ + if A * H ≤ R₂ then p else 0) % (A * B)) :
    R₃ = norm p r := by
  subst hB hH
  have hH : 0 < A * 2 ^ 63 := by positivity
  have hQ : A * 2 ^ 64 = 2 * (A * 2 ^ 63) := by ring
  have hpH : 2 * p < A * 2 ^ 63 := by omega_arith
  have rH : -(A * 2 ^ 63) ≤ r ∧ r < A * 2 ^ 63 := ⟨by omega_arith, by omega_arith⟩
  have eR := tc_eq hH rH.1 rH.2 hR0 (by rw [← hQ]; exact hR1) (by rw [← hQ]; exact hRr)
  have sR := tc_neg rH.1 rH.2 eR
  have eR₁ : R₁ = r + if r < 0 then p else 0 := by
    have hc : (if A * 2 ^ 63 ≤ R then p else 0) = if r < 0 then p else 0 := by simp only [sR]
    rw [hR₁, hc, eR, hQ]
    by_cases h : r < 0
    · simp only [h, ↓reduceIte]
      rw [show r + 2 * (A * 2 ^ 63) + p = r + p + 2 * (A * 2 ^ 63) * 1 by ring, Int.add_mul_emod_self_left,
        Int.emod_eq_of_lt (by omega_arith) (by omega_arith)]
    · simp only [h, ↓reduceIte, Int.add_zero]
      rw [Int.emod_eq_of_lt (by omega_arith) (by omega_arith)]
  obtain ⟨r₂, hr₂⟩ : ∃ r₂, r₂ = r + (if r < 0 then p else 0) - p := ⟨_, rfl⟩
  have r₂lo : -p ≤ r₂ := by rw [hr₂]; split <;> omega_arith
  have r₂hi : r₂ < p := by rw [hr₂]; split <;> omega_arith
  have eR₂ : R₂ = r₂ + if r₂ < 0 then 2 * (A * 2 ^ 63) else 0 := by
    refine tc_eq hH (by omega_arith) (by omega_arith) hR₂0 (by rw [← hQ]; exact hR₂1) ?_
    have h1 : (R₂ + p) % (A * 2 ^ 64) = (r₂ + p) % (A * 2 ^ 64) := by
      rw [hR₂, eR₁, Int.emod_eq_of_lt (a := r₂ + p) (by omega_arith) (by omega_arith), hr₂]; ring
    rw [← hQ]; exact Int.ModEq.add_right_cancel' p h1
  have sR₂ := tc_neg (by omega_arith) (by omega_arith) eR₂
  have hc₂ : (if A * 2 ^ 63 ≤ R₂ then p else 0) = if r₂ < 0 then p else 0 := by simp only [sR₂]
  rw [hR₃, hc₂, eR₂, hQ]
  unfold norm
  by_cases h2 : r₂ < 0
  · simp only [h2, ↓reduceIte]
    rw [show r₂ + 2 * (A * 2 ^ 63) + p = r₂ + p + 2 * (A * 2 ^ 63) * 1 by ring, Int.add_mul_emod_self_left,
      Int.emod_eq_of_lt (by omega_arith) (by omega_arith), hr₂]
    by_cases h : r < 0
    · simp only [h, ↓reduceIte]; ring
    · have h' : ¬ p ≤ r := by rw [hr₂] at h2; simp only [h, ↓reduceIte] at h2; omega_arith
      simp only [h, h', ↓reduceIte]; ring
  · simp only [h2, ↓reduceIte, Int.add_zero]
    rw [Int.emod_eq_of_lt (by omega_arith) (by omega_arith), hr₂]
    by_cases h : r < 0
    · rw [hr₂] at h2; simp only [h, ↓reduceIte] at h2; omega_arith
    · have h' : p ≤ r := by rw [hr₂] at h2; simp only [h, ↓reduceIte] at h2; omega_arith
      simp only [h, h', ↓reduceIte]; ring

/-- `mredRaw_words` on natural numbers, as words hold them (`B = 2^64`, `H = 2^63`). -/
theorem mredRaw_nat {A B H p m W k E R : Nat} {t : Int} (hB : B = 2 ^ 64) (hH : H = 2 ^ 63) (hA : 0 < A)
    (hp : 0 < p) (hpA : p < A) (hm : (p * m + 1) % B = 0) (ht : |t| ≤ 2 ^ 63 * p)
    (hW1 : W < A * B) (hWt : (W : Int) % ((A * B : Nat) : Int) = t % ((A * B : Nat) : Int))
    (hk : k = W % B * m % B)
    (hE : E = (W + A * B * (if A * H ≤ W then B - 1 else 0) + k * p) % (A * B * B))
    (hR : R = E / B) :
    (R : Int) % ((A * B : Nat) : Int) = mredRaw p m t % ((A * B : Nat) : Int) := by
  have hB1 : 1 ≤ B := by rw [hB]; exact Nat.one_le_two_pow
  have hk1 : k < B := by rw [hk]; exact Nat.mod_lt _ (by omega_arith)
  push_cast
  refine mredRaw_words (A := A) (B := B) (H := H) (p := p) (m := m) (t := t) (W := W) (k := k) (E := E) (R := R)
    (by rw [hB]; norm_num) (by rw [hH]; norm_num) (by exact_mod_cast hA)
    (by exact_mod_cast hp) (by exact_mod_cast hpA) (by exact_mod_cast hm) ht (by omega_arith) (by exact_mod_cast hW1)
    (by exact_mod_cast hWt) (by omega_arith) (by exact_mod_cast hk1) ?_ ?_ ?_
  · rw [hk]
    have h1 : W % B * m % B = W * m % B := by rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
    rw [h1]; push_cast; rw [Int.emod_emod_of_dvd _ (dvd_refl _)]
  · rw [hE, ← Nat.cast_mul A H, ite_natCast_le]; push_cast [Nat.cast_sub hB1]; rfl
  · rw [hR]; push_cast; rfl

/-- `norm_words` on natural numbers, as words hold them (`B = 2^64`, `H = 2^63`). -/
theorem norm_nat {A B H p R R₁ R₂ R₃ : Nat} {r : Int} (hB : B = 2 ^ 64) (hH : H = 2 ^ 63) (hA : 0 < A)
    (hpA : p < A) (hr0 : -(p : Int) < r) (hr1 : r < 2 * p)
    (hR1 : R < A * B) (hRr : (R : Int) % ((A * B : Nat) : Int) = r % ((A * B : Nat) : Int))
    (hR₁ : R₁ = (R + if A * H ≤ R then p else 0) % (A * B))
    (hR₂1 : R₂ < A * B) (hR₂ : (R₂ + p) % (A * B) = R₁)
    (hR₃ : R₃ = (R₂ + if A * H ≤ R₂ then p else 0) % (A * B)) :
    (R₃ : Int) = norm p r := by
  refine norm_words (A := A) (B := B) (H := H) (p := p) (r := r) (R := R) (R₁ := R₁) (R₂ := R₂) (R₃ := R₃)
    (by rw [hB]; norm_num) (by rw [hH]; norm_num) (by exact_mod_cast hA) (by exact_mod_cast hpA) hr0 hr1
    (by omega_arith) (by exact_mod_cast hR1) (by exact_mod_cast hRr) ?_ (by omega_arith) (by exact_mod_cast hR₂1) ?_ ?_
  · rw [hR₁, ← Nat.cast_mul A H, ite_natCast_le]; push_cast; rfl
  · rw [← hR₂]; push_cast; rfl
  · rw [hR₃, ← Nat.cast_mul A H, ite_natCast_le]; push_cast; rfl

end VG.Proof.Divstep
