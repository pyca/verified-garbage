module

public import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Pair

/-! # The matrix with the rows of `t̂` between its pairs

`matrixRows_ok`: `Kem16.kgMatrixRows`, from the interleaved invariant with
nothing done to the whole matrix, every row and the blocks `hashedBy (k² / 2)`
of `ek`. Pair `p` starts after `2 p` entries, `rowsBy p` rows and
`hashedBy p` blocks; it absorbs only blocks the rows before it encoded
(`hashed_le`), and the rows after it use only entries it or its predecessors
sampled. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Impl.MlKem.AArch64.Kem16 (rowsBy hashedBy kgRows kgPair kgMatrixRows)

variable {P : KemLay}

theorem rowsBy_mono (P : KemLay) (p : Nat) : rowsBy P p ≤ rowsBy P (p + 1) := by
  simp only [rowsBy]
  have := Nat.div_le_div_right (c := P.k) (show 2 * p ≤ 2 * (p + 1) by omega)
  omega

/-- The first `rowsBy p` rows use only the first `2 p` entries. -/
theorem rowsBy_mul (P : KemLay) (p : Nat) : P.k * rowsBy P p ≤ 2 * p := by
  simp only [rowsBy]
  exact Nat.le_trans (Nat.mul_le_mul_left _ (Nat.min_le_right _ _)) (Nat.mul_div_le _ _)

theorem rowsBy_le (P : KemLay) (p : Nat) : rowsBy P p ≤ P.k := Nat.min_le_left _ _

/-- The blocks absorbed before pair `p` are among those the rows before it encoded. -/
theorem hashed_le (P : KemLay) : ∀ p, 136 * hashedBy P p ≤ 384 * rowsBy P p
  | 0 => by simp [hashedBy]
  | p + 1 => by
    have ih := hashed_le P p
    have hm := rowsBy_mono P p
    have hA : hashedBy P p ≤ 384 * rowsBy P p / 136 := (Nat.le_div_iff_mul_le (by decide)).2 (by omega)
    have hB : 136 * (384 * rowsBy P p / 136) ≤ 384 * rowsBy P p := Nat.mul_div_le _ _
    simp only [hashedBy]
    have := Nat.min_le_right 3 (384 * rowsBy P p / 136 - hashedBy P p)
    omega

theorem hashed_succ (P : KemLay) (p : Nat) :
    hashedBy P (p + 1) = hashedBy P p + (hashedBy P (p + 1) - hashedBy P p) := by
  simp only [hashedBy]; omega

/-- `n` steps, each a list of programs, by an invariant `I i` before step `i`. -/
theorem wps_flatMap_range {f : Nat → List (Prog isa)} {I : Nat → State → Prop} :
    ∀ {n : Nat}, (∀ i < n, ∀ s, I i s → WPs (f i) s (I (i + 1))) →
      ∀ {s : State}, I 0 s → WPs ((List.range n).flatMap f) s (I n)
  | 0, _, _, h => h
  | n + 1, hf, _, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WPs.append (WPs.mono (wps_flatMap_range (fun i hi => hf i (by omega)) h)
      fun s' h' => hf n (by omega) s' h')

/-- Rows `a` to `a + d - 1` of `t̂`, once the matrix holds their entries. -/
theorem rows_ok {s₀ : State} (hp : Pre P s₀) (hr : Noise.Room P) {n h : Nat} :
    ∀ (d a : Nat), a + d ≤ P.k → P.k * (a + d) ≤ n → ∀ {s : State}, IL P s₀ n a h s →
      WPs (kgRows P a (a + d)) s (IL P s₀ n (a + d) h)
  | 0, a, _, _, _, H => by
    simp only [kgRows, Nat.add_zero, Nat.sub_self, List.range'_zero, List.map_nil, WPs]
    exact H
  | d + 1, a, hd, hn, s, H => by
    have e : kgRows P a (a + (d + 1)) = Kem16.kgRow P a :: kgRows P (a + 1) (a + 1 + d) := by
      simp only [kgRows, show a + (d + 1) - a = d + 1 by omega, show a + 1 + d - (a + 1) = d by omega,
        List.range'_succ, List.map_cons]
    rw [e]
    refine WPs.cons (WP.mono (row_step hp hr (by omega)
      (Nat.le_trans (Nat.mul_le_mul_left _ (by omega)) hn) H) fun t ht => ?_)
    have e2 : a + 1 + d = a + (d + 1) := by omega
    have r := rows_ok hp hr d (a + 1) (by omega) (by rw [e2]; exact hn) ht
    exact WPs.mono r fun u hu => by rwa [e2] at hu

/-- **The matrix and the rows of `t̂`.** -/
theorem matrixRows_ok {s₀ s : State} (hp : Pre P s₀) (hk : Stk128K P s₀) (hr : Noise.Room P)
    (H : IL P s₀ 0 0 0 s) :
    WPs (kgMatrixRows P) s (IL P s₀ (P.k * P.k) P.k (hashedBy P (P.k * P.k / 2))) := by
  have hw := hp.wf
  have hf := hw.facts
  have hek : 384 * P.k < P.ekLen := by simp only [KemLay.ekLen]; omega
  have pairs := wps_flatMap_range (n := P.k * P.k / 2)
    (I := fun p s => IL P s₀ (2 * p) (rowsBy P p) (hashedBy P p) s)
    (f := fun p => kgPair P p :: kgRows P (rowsBy P p) (rowsBy P (p + 1)))
    (fun p hp' s Hs => by
      have hmono := rowsBy_mono P p
      have hle := rowsBy_le P (p + 1)
      have h2 := hashed_le P (p + 1)
      have hrk := rowsBy_le P p
      refine WPs.cons (WP.mono (pair_step hp hk hr (p := p) (r := rowsBy P p) (h := hashedBy P p)
        (m := hashedBy P (p + 1) - hashedBy P p) (by omega)
        (by simp only [hashedBy]; omega) (fun k hk' => ?_) ?_ Hs) fun t ht => ?_)
      · have := Nat.mul_le_mul_left 384 hrk
        have h3 := hashed_le P (p + 1)
        simp only [hashedBy] at h3 hk' ⊢
        have : 136 * (384 * rowsBy P p / 136) ≤ 384 * rowsBy P p := Nat.mul_div_le _ _
        omega
      · rw [← hashed_succ]
        have hA : hashedBy P p ≤ 384 * rowsBy P p / 136 :=
          (Nat.le_div_iff_mul_le (by decide)).2 (by have := hashed_le P p; omega)
        have hB : 136 * (384 * rowsBy P p / 136) ≤ 384 * rowsBy P p := Nat.mul_div_le _ _
        simp only [hashedBy]
        have := Nat.min_le_right 3 (384 * rowsBy P p / 136 - hashedBy P p)
        omega
      · rw [← hashed_succ] at ht
        have r := rows_ok hp hr (n := 2 * p + 2) (rowsBy P (p + 1) - rowsBy P p) (rowsBy P p) (by omega)
          (by rw [Nat.add_sub_cancel' hmono]; exact Nat.le_trans (rowsBy_mul P (p + 1)) (by omega)) ht
        rw [Nat.add_sub_cancel' hmono] at r
        exact r) (by simpa [rowsBy, hashedBy] using H)
  rw [kgMatrixRows]
  refine WPs.append (WPs.mono pairs fun t ht => ?_)
  by_cases ho : P.k * P.k % 2 = 1
  · rw [ite_eq_left ho]
    have e : 2 * (P.k * P.k / 2) = P.k * P.k - 1 := by omega
    rw [e] at ht
    refine WPs.cons (WP.mono (last_step hp hr ho ht) fun u hu => ?_)
    have hle := rowsBy_le P (P.k * P.k / 2)
    have r := rows_ok hp hr (n := P.k * P.k) (P.k - rowsBy P (P.k * P.k / 2)) (rowsBy P (P.k * P.k / 2))
      (by omega) (by rw [Nat.add_sub_cancel' hle]) hu
    rwa [Nat.add_sub_cancel' hle] at r
  · rw [ite_eq_right ho]
    have e : 2 * (P.k * P.k / 2) = P.k * P.k := by omega
    have er : rowsBy P (P.k * P.k / 2) = P.k := by
      simp only [rowsBy, e, Nat.mul_div_cancel_left _ (show 0 < P.k by omega), Nat.min_self]
    rw [e, er] at ht
    exact ht

end VG.Proof.MlKem.AArch64.KeyGen
