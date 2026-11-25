module

public import VerifiedGarbage.Proof.Gcm.Clmul.Arith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Carry-less products from integer products

Untrusted: everything here is checked by Lean. If the set bits of `a` are all
at positions congruent to `i` modulo `k`, those of `b` at positions congruent
to `j`, and fewer than `2ᵏ` pairs of them meet at any position, the integer
product of `a` and `b` has at each position congruent to `i + j` the bit of
the carry-less product: the count of the pairs that meet at a position does
not reach the next position of the class. (`testBit_sum`, `getLsbD_mul`.)
-/

@[expose] public section

namespace VG.Proof.Gcm.Spread

open Polynomial VG.VectorCrypto VG.Proof.Gcm.Poly VG.Proof.Gcm.Clmul

/-! ## Digits -/

/-- Digits `c t < 2ᵏ`, `k` bits apart from bit `r`. -/
theorem sum_lt (k r : Nat) (c : Nat → Nat) (n : Nat) (hc : ∀ t < n, c t < 2 ^ k) :
    ∑ t ∈ Finset.range n, c t * 2 ^ (k * t + r) < 2 ^ (k * n + r) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 := ih fun t ht => hc t (Nat.lt_succ_of_lt ht)
    have h2 := hc n (Nat.lt_succ_self n)
    have h3 : 2 ^ (k * (n + 1) + r) = 2 ^ k * 2 ^ (k * n + r) := by rw [← pow_add]; ring_nf
    rw [h3]
    have h4 : (c n + 1) * 2 ^ (k * n + r) ≤ 2 ^ k * 2 ^ (k * n + r) := Nat.mul_le_mul_right _ h2
    rw [Nat.add_mul, Nat.one_mul] at h4
    omega

theorem testBit_sum (k r : Nat) (hk : 0 < k) (c : Nat → Nat) (n : Nat) (hc : ∀ t < n, c t < 2 ^ k)
    {t : Nat} (ht : t < n) :
    (∑ t ∈ Finset.range n, c t * 2 ^ (k * t + r)).testBit (k * t + r) = decide (c t % 2 = 1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hl := sum_lt k r c n fun t ht => hc t (Nat.lt_succ_of_lt ht)
    rw [Nat.add_comm, Nat.mul_comm (c n)]
    by_cases h : t = n
    · subst h
      rw [Nat.testBit_two_pow_mul_add _ hl]
      simp [Nat.testBit_zero]
    · have h' : t < n := by omega
      rw [Nat.testBit_two_pow_mul_add _ hl, ite_eq_left]
      · exact ih (fun t ht => hc t (Nat.lt_succ_of_lt ht)) h'
      · have := Nat.mul_lt_mul_of_pos_left h' hk
        omega

/-! ## Polynomials of the bits of a word, the least significant first -/

/-- With natural coefficients. -/
noncomputable def np {w : Nat} (v : BitVec w) : Polynomial ℕ :=
  ∑ i ∈ Finset.range w, if v.getLsbD i then X ^ i else 0

theorem coeff_np {w : Nat} (v : BitVec w) (d : Nat) : (np v).coeff d = if v.getLsbD d then 1 else 0 := by
  simp only [np, finsetSum_coeff]
  have : ∀ i, (if v.getLsbD i then (X ^ i : Polynomial ℕ) else 0).coeff d =
      if d = i then (if v.getLsbD d then 1 else 0) else 0 := by
    intro i; split_ifs <;> simp_all [coeff_X_pow]
  simp only [this, Finset.sum_ite_eq, Finset.mem_range]
  by_cases h : d < w
  · simp only [h, ite_true]
  · simp only [h, ite_false, BitVec.getLsbD_of_ge v d (Nat.le_of_not_lt h), Bool.false_eq_true]

theorem coeff_np_le {w : Nat} (v : BitVec w) (d : Nat) : (np v).coeff d ≤ 1 := by
  rw [coeff_np]; split_ifs <;> simp

/-- Over GF(2). -/
noncomputable def lp {w : Nat} (v : BitVec w) : P := (np v).map (Nat.castRingHom (ZMod 2))

theorem coeff_lp {w : Nat} (v : BitVec w) (d : Nat) : (lp v).coeff d = bit (v.getLsbD d) := by
  rw [lp, coeff_map, coeff_np, bit]; split_ifs <;> simp

theorem lp_ext {w : Nat} {a b : BitVec w} (h : lp a = lp b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  have := congrArg (fun p : P => p.coeff i) h
  simp only [coeff_lp] at this
  exact bit_inj this

theorem lp_xor {w : Nat} (a b : BitVec w) : lp (a ^^^ b) = lp a + lp b := by
  ext k; simp only [coeff_add, coeff_lp, BitVec.getLsbD_xor, bit_xor]

theorem lp_zero (w : Nat) : lp (0#w) = 0 := by
  ext k; simp [coeff_lp, bit]

theorem lp_shl (b : BitVec 64) {j : Nat} (hj : j < 64) : lp (b.setWidth 128 <<< j) = X ^ j * lp b := by
  ext d
  rw [coeff_lp, coeff_X_pow_mul', coeff_lp, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases h : j ≤ d
  · simp only [h, ite_true, decide_eq_false (show ¬ d < j by omega), Bool.not_false, Bool.and_true]
    by_cases h2 : d < 128
    · simp only [h2, decide_true, Bool.true_and, decide_eq_true (show d - j < 128 by omega)]
    · simp only [h2, decide_false, Bool.false_and]
      rw [BitVec.getLsbD_of_ge b (d - j) (by omega)]
  · simp [h, decide_eq_true (show d < j by omega), bit]

theorem lp_clSteps (a b : BitVec 64) {k : Nat} (hk : k ≤ 64) :
    lp (clSteps a b k) = (∑ i ∈ Finset.range k, if a.getLsbD i then X ^ i else 0) * lp b := by
  induction k with
  | zero => simp only [clSteps, List.range_zero, List.foldl_nil, Finset.range_zero, Finset.sum_empty, zero_mul]; exact lp_zero 128
  | succ k ih =>
    have e : clSteps a b (k + 1) =
        if a.getLsbD k then clSteps a b k ^^^ (b.setWidth 128 <<< k) else clSteps a b k := by
      simp only [clSteps, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [e, Finset.sum_range_succ]
    split_ifs
    · rw [lp_xor, ih (by omega), lp_shl b (by omega), add_mul]
    · rw [ih (by omega), add_zero]

theorem lp_eq_sum {w : Nat} (a : BitVec w) : lp a = ∑ i ∈ Finset.range w, if a.getLsbD i then X ^ i else 0 := by
  rw [lp, np, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem lp_polyMul (a b : BitVec 64) : lp (polyMul a b) = lp a * lp b := by
  rw [show polyMul a b = clSteps a b 64 from rfl, lp_clSteps a b (Nat.le_refl _), lp_eq_sum a]

theorem polyMul_xor_left (a b c : BitVec 64) : polyMul (a ^^^ b) c = polyMul a c ^^^ polyMul b c :=
  lp_ext (by simp only [lp_polyMul, lp_xor, add_mul])

theorem polyMul_xor_right (a b c : BitVec 64) : polyMul a (b ^^^ c) = polyMul a b ^^^ polyMul a c :=
  lp_ext (by simp only [lp_polyMul, lp_xor, mul_add])

/-! ## The product of two classes -/

theorem toNat_eq_eval {w : Nat} (v : BitVec w) : v.toNat = (np v).eval 2 := by
  rw [np, eval_finsetSum]
  induction w with
  | zero => simp [BitVec.eq_nil v]
  | succ w ih =>
    rw [Finset.sum_range_succ]
    have h := ih (v.setWidth w)
    have e : ∀ i ∈ Finset.range w, eval 2 (if (v.setWidth w).getLsbD i then (X ^ i : Polynomial ℕ) else 0) =
        eval 2 (if v.getLsbD i then X ^ i else 0) := by
      intro i hi
      rw [BitVec.getLsbD_setWidth, decide_eq_true (Finset.mem_range.mp hi), Bool.true_and]
    rw [Finset.sum_congr rfl e] at h
    rw [← h, BitVec.toNat_setWidth]
    have hv := v.isLt
    have hm := Nat.mod_add_div v.toNat (2 ^ w)
    have hb : v.getLsbD w = decide (v.toNat / 2 ^ w = 1) := by
      rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
      have : v.toNat / 2 ^ w < 2 := Nat.div_lt_of_lt_mul (by rwa [← pow_succ])
      rw [Nat.mod_eq_of_lt this]
    have hl : v.toNat / 2 ^ w < 2 := Nat.div_lt_of_lt_mul (by rwa [← pow_succ])
    rw [hb]
    by_cases h1 : v.toNat / 2 ^ w = 1
    · simp only [h1, decide_true, ite_true, eval_pow, eval_X]; rw [h1, Nat.mul_one] at hm; exact hm.symm
    · have h0 : v.toNat / 2 ^ w = 0 := Nat.lt_one_iff.mp (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hl) h1)
      simp only [h0, Nat.zero_ne_one, decide_false, Bool.false_eq_true, ite_false, eval_zero]
      rw [h0, Nat.mul_zero] at hm; exact hm.symm

/-- The set bits of `a` are at positions congruent to `i` modulo `k`. -/
def InClass {w : Nat} (k i : Nat) (a : BitVec w) : Prop := ∀ p, a.getLsbD p = true → p % k = i

theorem coeff_mul_class {k i j : Nat} {a b : BitVec 64} (ha : InClass k i a) (hb : InClass k j b) {d : Nat}
    (hd : d % k ≠ (i + j) % k) : (np a * np b).coeff d = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun ⟨p, q⟩ h => ?_
  rw [Finset.mem_antidiagonal] at h
  simp only [coeff_np]
  by_cases h1 : a.getLsbD p = true
  · by_cases h2 : b.getLsbD q = true
    · refine absurd ?_ hd
      rw [← h, Nat.add_mod, ha p h1, hb q h2]
    · simp [h2]
  · simp [h1]

theorem coeff_mul_lt {k i : Nat} {a b : BitVec 64} (ha : InClass k i a) (hn : 63 / k + 1 < 2 ^ k) (d : Nat) :
    (np a * np b).coeff d < 2 ^ k := by
  apply Nat.lt_of_le_of_lt _ hn
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun p q => (np a).coeff p * (np b).coeff q) d]
  have h : ∀ p ∈ Finset.range d.succ, (np a).coeff p * (np b).coeff (d - p) ≤ if a.getLsbD p then 1 else 0 := by
    intro p _
    have := coeff_np_le b (d - p)
    rw [coeff_np a]
    split_ifs
    · omega
    · simp
  calc _ ≤ ∑ p ∈ Finset.range d.succ, (if a.getLsbD p = true then 1 else 0) := Finset.sum_le_sum h
    _ = ((Finset.range d.succ).filter fun p => a.getLsbD p = true).card := (Finset.card_filter _ _).symm
    _ ≤ ((Finset.range (63 / k + 1)).image fun t => k * t + i).card := by
        refine Finset.card_le_card fun p hp => ?_
        simp only [Finset.mem_filter] at hp
        have hc := ha p hp.2
        have h64 : p < 64 := BitVec.lt_of_getLsbD hp.2
        rw [Finset.mem_image]
        refine ⟨p / k, ?_, ?_⟩
        · rw [Finset.mem_range]
          exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
        · rw [← hc]; exact Nat.div_add_mod p k
    _ ≤ _ := by
        refine Finset.card_image_le.trans ?_
        rw [Finset.card_range]

theorem toNat_mul_eval (a b : BitVec 64) : a.toNat * b.toNat = (np a * np b).eval 2 := by
  rw [eval_mul, ← toNat_eq_eval, ← toNat_eq_eval]

/-- A bit of the integer product, in the class of the product, is the bit of
the carry-less product. -/
theorem getLsbD_mul {k i j : Nat} (hk : 0 < k) {a b : BitVec 64} (ha : InClass k i a) (hb : InClass k j b)
    (hn : 63 / k + 1 < 2 ^ k) {p : Nat} (hp : p < 128) (hpc : p % k = (i + j) % k) :
    (a.setWidth 128 * b.setWidth 128).getLsbD p = (polyMul a b).getLsbD p := by
  have hm : (a.setWidth 128 * b.setWidth 128).toNat = a.toNat * b.toNat := by
    rw [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (show a.toNat < 2 ^ 128 by have := a.isLt; omega),
      Nat.mod_eq_of_lt (show b.toNat < 2 ^ 128 by have := b.isLt; omega)]
    refine Nat.mod_eq_of_lt ?_
    have := Nat.mul_lt_mul'' a.isLt b.isLt
    rwa [← pow_add] at this
  have hdeg : (np a * np b).natDegree < k * 128 + (i + j) % k := by
    have hda : ∀ c : BitVec 64, (np c).natDegree ≤ 63 := fun c => by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro n hn
      rw [coeff_np, BitVec.getLsbD_of_ge c n (by omega)]; rfl
    have := natDegree_mul_le (p := np a) (q := np b)
    have := hda a; have := hda b
    have := Nat.mul_le_mul_right 128 hk
    omega
  have hs : a.toNat * b.toNat =
      ∑ t ∈ Finset.range 128, (np a * np b).coeff (k * t + (i + j) % k) * 2 ^ (k * t + (i + j) % k) := by
    rw [toNat_mul_eval, eval_eq_sum_range' hdeg]
    symm
    refine Finset.sum_of_injOn (fun t => k * t + (i + j) % k) ?_ ?_ ?_ ?_
    · intro x _ y _ h
      exact Nat.eq_of_mul_eq_mul_left hk (Nat.add_right_cancel h)
    · intro t ht
      simp only [Finset.coe_range, Set.mem_Iio] at ht ⊢
      have := Nat.mul_lt_mul_of_pos_left ht hk
      omega
    · intro d hd hni
      rw [coeff_mul_class ha hb, zero_mul]
      intro hc
      refine hni ⟨d / k, ?_, ?_⟩
      · rw [Finset.mem_range] at hd
        rw [Finset.mem_coe, Finset.mem_range]
        have h2 := Nat.div_add_mod d k
        rw [hc] at h2
        exact Nat.lt_of_mul_lt_mul_left (a := k) (by omega)
      · show k * (d / k) + (i + j) % k = d
        rw [← hc]; exact Nat.div_add_mod d k
    · intro t _; rfl
  have hpd : p = k * (p / k) + (i + j) % k := by rw [← hpc]; exact (Nat.div_add_mod p k).symm
  have hpk : p / k < 128 := Nat.lt_of_le_of_lt (Nat.div_le_self p k) hp
  have h1 : (a.setWidth 128 * b.setWidth 128).getLsbD p =
      decide ((np a * np b).coeff p % 2 = 1) := by
    rw [BitVec.getLsbD, hm, hs]
    conv_lhs => rw [hpd]
    rw [testBit_sum k _ hk (fun t => (np a * np b).coeff (k * t + (i + j) % k)) 128
      (fun t _ => coeff_mul_lt ha hn _) hpk, ← hpd]
  have h2 : bit ((polyMul a b).getLsbD p) = (((np a * np b).coeff p : ℕ) : ZMod 2) := by
    rw [← coeff_lp, lp_polyMul, lp, lp, ← Polynomial.map_mul, coeff_map]; rfl
  rw [h1]
  apply bit_inj
  rw [h2, bit]
  rcases Nat.mod_two_eq_zero_or_one ((np a * np b).coeff p) with h | h
  · simp only [h, Nat.zero_ne_one, decide_false, Bool.false_eq_true, ite_false]
    exact ((ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero h)).symm
  · simp only [h, decide_true, ite_true]
    have : (((np a * np b).coeff p : ℕ) : ZMod 2) = ((1 : ℕ) : ZMod 2) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr (by show _ % 2 = 1 % 2; rw [h])
    rw [this]; rfl

/-- Outside its class, the carry-less product of two classes is zero. -/
theorem getLsbD_polyMul_class {k i j : Nat} {a b : BitVec 64} (ha : InClass k i a) (hb : InClass k j b) {p : Nat}
    (hpc : p % k ≠ (i + j) % k) : (polyMul a b).getLsbD p = false := by
  apply bit_inj
  rw [← coeff_lp, lp_polyMul, lp, lp, ← Polynomial.map_mul, coeff_map, coeff_mul_class ha hb hpc]
  simp [bit]

/-! ## Five classes of 64-bit words -/

/-- The positions congruent to `r` modulo 5 of a word. -/
def m5 (r : Nat) : BitVec 64 :=
  match r with
  | 0 => 0x1084210842108421#64 | 1 => 0x2108421084210842#64 | 2 => 0x4210842108421084#64
  | 3 => 0x8421084210842108#64 | _ => 0x0842108421084210#64

/-- The same of 128 bits: bit 64 is of class 4. -/
def M5 (r : Nat) : BitVec 128 := m5 ((r + 1) % 5) ++ m5 r

/-- The integer product of class `i` of `a` and class `j` of `b`. -/
def cp (a b : BitVec 64) (i j : Nat) : BitVec 128 :=
  (a &&& m5 i).setWidth 128 * (b &&& m5 j).setWidth 128

/-- The products that meet in class `r`. -/
def meet (a b : BitVec 64) (r : Nat) : BitVec 128 :=
  cp a b 0 (r % 5) ^^^ cp a b 1 ((r + 4) % 5) ^^^ cp a b 2 ((r + 3) % 5) ^^^ cp a b 3 ((r + 2) % 5) ^^^
    cp a b 4 ((r + 1) % 5)

/-- The carry-less product, from 25 integer products. -/
def mul5 (a b : BitVec 64) : BitVec 128 :=
  (meet a b 0 &&& M5 0) ^^^ (meet a b 1 &&& M5 1) ^^^ (meet a b 2 &&& M5 2) ^^^ (meet a b 3 &&& M5 3) ^^^
    (meet a b 4 &&& M5 4)

theorem m5_class : ∀ i < 5, ∀ p < 64, (m5 i).getLsbD p = decide (p % 5 = i) := by decide +kernel

theorem M5_class : ∀ i < 5, ∀ p < 128, (M5 i).getLsbD p = decide (p % 5 = i) := by decide +kernel

theorem inClass_m5 (a : BitVec 64) {i : Nat} (hi : i < 5) : InClass 5 i (a &&& m5 i) := by
  intro p hp
  have h64 : p < 64 := BitVec.lt_of_getLsbD hp
  rw [BitVec.getLsbD_and, m5_class i hi p h64, Bool.and_eq_true, decide_eq_true_eq] at hp
  exact hp.2

theorem cp_mask (a b : BitVec 64) {i j r : Nat} (hi : i < 5) (hj : j < 5) (hr : r < 5) (h : (i + j) % 5 = r) :
    cp a b i j &&& M5 r = polyMul (a &&& m5 i) (b &&& m5 j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro p hp
  rw [BitVec.getLsbD_and, M5_class r hr p hp]
  by_cases hc : p % 5 = r
  · rw [decide_eq_true hc, Bool.and_true]
    exact getLsbD_mul (by decide) (inClass_m5 a hi) (inClass_m5 b hj) (by decide) hp (hc.trans h.symm)
  · rw [decide_eq_false hc, Bool.and_false]
    exact (getLsbD_polyMul_class (inClass_m5 a hi) (inClass_m5 b hj) (fun e => hc (e.trans h))).symm

theorem and_xor {w : Nat} (a b c : BitVec w) : a &&& (b ^^^ c) = (a &&& b) ^^^ (a &&& c) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, Bool.and_xor_distrib_left]

theorem xor_and {w : Nat} (a b c : BitVec w) : (a ^^^ b) &&& c = (a &&& c) ^^^ (b &&& c) := by
  rw [BitVec.and_comm, and_xor, BitVec.and_comm c a, BitVec.and_comm c b]

theorem split5 (a : BitVec 64) :
    (a &&& m5 0) ^^^ (a &&& m5 1) ^^^ (a &&& m5 2) ^^^ (a &&& m5 3) ^^^ (a &&& m5 4) = a := by
  rw [← and_xor, ← and_xor, ← and_xor, ← and_xor, show m5 0 ^^^ m5 1 ^^^ m5 2 ^^^ m5 3 ^^^ m5 4 = BitVec.allOnes 64 by decide,
    BitVec.and_allOnes]

theorem mul5_eq (a b : BitVec 64) : mul5 a b = polyMul a b := by
  have hm : ∀ r < 5, meet a b r &&& M5 r =
      polyMul (a &&& m5 0) (b &&& m5 (r % 5)) ^^^ polyMul (a &&& m5 1) (b &&& m5 ((r + 4) % 5)) ^^^
      polyMul (a &&& m5 2) (b &&& m5 ((r + 3) % 5)) ^^^ polyMul (a &&& m5 3) (b &&& m5 ((r + 2) % 5)) ^^^
      polyMul (a &&& m5 4) (b &&& m5 ((r + 1) % 5)) := by
    intro r hr
    rw [meet, xor_and, xor_and, xor_and,
      xor_and,
      cp_mask a b (by decide) (Nat.mod_lt _ (by decide)) hr (by omega),
      cp_mask a b (by decide) (Nat.mod_lt _ (by decide)) hr (by omega),
      cp_mask a b (by decide) (Nat.mod_lt _ (by decide)) hr (by omega),
      cp_mask a b (by decide) (Nat.mod_lt _ (by decide)) hr (by omega),
      cp_mask a b (by decide) (Nat.mod_lt _ (by decide)) hr (by omega)]
  rw [mul5, hm 0 (by decide), hm 1 (by decide), hm 2 (by decide), hm 3 (by decide), hm 4 (by decide)]
  simp only [Nat.reduceMod, Nat.reduceAdd]
  apply lp_ext
  conv_rhs => rw [lp_polyMul, ← split5 a, ← split5 b]
  simp only [lp_xor, lp_polyMul]
  ring

/-! ## The reduction by shifts -/

theorem polyMul_poly (w : BitVec 64) :
    polyMul w Impl.Gcm.Clmul.poly =
      (w.setWidth 128 <<< 63) ^^^ (w.setWidth 128 <<< 62) ^^^ (w.setWidth 128 <<< 57) := by
  apply lp_ext
  have hp : lp Impl.Gcm.Clmul.poly = X ^ 63 + X ^ 62 + X ^ 57 := by
    have hb : ∀ d < 64, Impl.Gcm.Clmul.poly.getLsbD d = (d = 63 || d = 62 || d = 57) := by decide +kernel
    ext d
    rw [coeff_lp]
    simp only [coeff_add, coeff_X_pow]
    by_cases hd : d < 64
    · rw [hb d hd]
      by_cases h1 : d = 63
      · subst h1; decide
      · by_cases h2 : d = 62
        · subst h2; decide
        · by_cases h3 : d = 57
          · subst h3; decide
          · simp [h1, h2, h3, bit]
    · rw [BitVec.getLsbD_of_ge _ d (by omega)]
      simp [show d ≠ 63 by omega, show d ≠ 62 by omega, show d ≠ 57 by omega, bit]
  rw [lp_polyMul, hp, lp_xor, lp_xor, lp_shl w (by decide), lp_shl w (by decide), lp_shl w (by decide)]
  ring

theorem vdword_shl_0 (w : BitVec 64) (j : Nat) : vdword (w.setWidth 128 <<< j) 0 = w <<< j := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vdword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, hi, decide_true,
    Bool.true_and, Nat.mul_zero, Nat.zero_add, show i < 128 by omega, show i - j < 128 by omega]

theorem vdword_shl_1 (w : BitVec 64) {j : Nat} (hj : j ≤ 64) : vdword (w.setWidth 128 <<< j) 1 = w >>> (64 - j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [vdword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and, Nat.mul_one, show 64 + i < 128 by omega,
    show ¬ 64 + i < j by omega, decide_false, Bool.not_false, show 64 + i - j < 128 by omega]
  exact congrArg _ (by omega)

theorem poly_0 (w : BitVec 64) : vdword (polyMul w Impl.Gcm.Clmul.poly) 0 = w <<< 63 ^^^ w <<< 62 ^^^ w <<< 57 := by
  rw [polyMul_poly, vdword_xor, vdword_xor, vdword_shl_0, vdword_shl_0, vdword_shl_0]

theorem poly_1 (w : BitVec 64) : vdword (polyMul w Impl.Gcm.Clmul.poly) 1 = w >>> 1 ^^^ w >>> 2 ^^^ w >>> 7 := by
  rw [polyMul_poly, vdword_xor, vdword_xor, vdword_shl_1 w (by decide), vdword_shl_1 w (by decide),
    vdword_shl_1 w (by decide)]

/-- The word above, and the two words, of the fold of `w`. -/
def up (w : BitVec 64) : BitVec 64 := w >>> 1 ^^^ w >>> 2 ^^^ w >>> 7
def dn (w : BitVec 64) : BitVec 64 := w <<< 63 ^^^ w <<< 62 ^^^ w <<< 57

/-- The product of `y₁ : y₀` and the adjusted key `k₁ : k₀` (the first bits in
`y₁`), from the three products of Karatsuba's method `l`, `h` and `c`,
reduced: `(y₁, y₀)`. -/
def redW (l h c : BitVec 128) : BitVec 64 × BitVec 64 :=
  let m := c ^^^ l ^^^ h
  let u := vdword m 0 ^^^ vdword l 1 ^^^ dn (vdword l 0)
  (vdword h 1 ^^^ u ^^^ up u, vdword h 0 ^^^ vdword m 1 ^^^ vdword l 0 ^^^ up (vdword l 0) ^^^ dn u)

def mulW (y1 y0 k1 k0 : BitVec 64) : BitVec 64 × BitVec 64 :=
  redW (polyMul y0 k0) (polyMul y1 k1) (polyMul (y0 ^^^ y1) (k0 ^^^ k1))

/-- The adjusted key, `H · x⁻¹`. -/
def keyW1 (h1 h0 : BitVec 64) : BitVec 64 := h1 <<< 1 ^^^ h0 >>> 63 ^^^ dn (h1 >>> 63)
def keyW0 (h1 h0 : BitVec 64) : BitVec 64 := h0 <<< 1 ^^^ h1 >>> 63

theorem reduce_words (l m h : BitVec 128) :
    reduce ⟨l, m, h⟩ =
      (let u := vdword m 0 ^^^ vdword l 1 ^^^ dn (vdword l 0)
       ofVDwords (vdword h 1 ^^^ u ^^^ up u)
        (vdword h 0 ^^^ vdword m 1 ^^^ vdword l 0 ^^^ up (vdword l 0) ^^^ dn u)) := by
  have e0 : vdword ((m ^^^ ext8 l l) ^^^ polyMul (vdword l 0) Impl.Gcm.Clmul.poly) 0 =
      vdword m 0 ^^^ vdword l 1 ^^^ dn (vdword l 0) := by
    rw [vdword_xor, vdword_xor, vdword_ext8_0, poly_0, dn]
  have e1 : vdword ((m ^^^ ext8 l l) ^^^ polyMul (vdword l 0) Impl.Gcm.Clmul.poly) 1 =
      vdword m 1 ^^^ vdword l 0 ^^^ up (vdword l 0) := by
    rw [vdword_xor, vdword_xor, vdword_ext8_1, poly_1, up]
  simp only [reduce]
  generalize (m ^^^ ext8 l l) ^^^ polyMul (vdword l 0) Impl.Gcm.Clmul.poly = u at e0 e1 ⊢
  rw [vdwords (ext8 h h ^^^ u ^^^ ext8 (polyMul (vdword u 0) Impl.Gcm.Clmul.poly) _)]
  simp only [vdword_xor, vdword_ext8_0, vdword_ext8_1, e1, e0, poly_0, poly_1, ofVDwords]
  simp only [up, dn, BitVec.xor_assoc]

theorem mulW_mulV (y1 y0 k1 k0 : BitVec 64) :
    ofVDwords (mulW y1 y0 k1 k0).1 (mulW y1 y0 k1 k0).2 = mulV (ofVDwords y1 y0) (k1 ++ k0) := by
  have hm : polyMul (y0 ^^^ y1) (k0 ^^^ k1) ^^^ polyMul y0 k0 ^^^ polyMul y1 k1 =
      polyMul y1 k0 ^^^ polyMul y0 k1 := by
    apply lp_ext
    have h2 : (2 : P) = 0 := CharTwo.two_eq_zero
    simp only [lp_xor, lp_polyMul]
    linear_combination (lp y0 * lp k0 + lp y1 * lp k1) * h2
  have hp : Clmul.Prod.zero.acc (ofVDwords y1 y0) (ext8 (k1 ++ k0) (k1 ++ k0)) (k1 ++ k0) =
      ⟨polyMul y0 k0, polyMul y1 k0 ^^^ polyMul y0 k1, polyMul y1 k1⟩ := by
    rw [Clmul.Prod.acc, Clmul.Prod.zero, vdword_ext8_0, vdword_ext8_1, ofVDwords, vdword_append_0, vdword_append_1,
      vdword_append_0, vdword_append_1]
    show Clmul.Prod.mk (0#128 ^^^ _) (0#128 ^^^ _ ^^^ _) (0#128 ^^^ _) = _
    rw [BitVec.zero_xor, BitVec.zero_xor, BitVec.zero_xor]
  rw [mulV, hp, reduce_words, mulW, redW, hm]

theorem ρ_words (y1 y0 : BitVec 64) : ρ (ofVDwords y1 y0) = φ (y1 ++ y0) := by
  rw [ρ, ofVDwords, vdword_append_0, vdword_append_1, φ_append]

theorem up_ushr63 (a : BitVec 64) : up (a >>> 63) = 0#64 := by
  have h : ∀ b : Bool, up (if b then 1#64 else 0#64) = 0#64 := by decide
  rw [ushr63]; exact h _

theorem x_key (h1 h0 : BitVec 64) : x * φ (keyW1 h1 h0 ++ keyW0 h1 h0) = φ (h1 ++ h0) := by
  have ht := twist_ρ h1 h0
  rw [← ρ_xor, ← ρ_xor] at ht
  rw [← ρ_words h1 h0, ← ht, ← ρ_words]
  congr 2
  rw [vdwords (ofVDwords (keyW1 h1 h0) (keyW0 h1 h0)), vdwords (_ ^^^ _ ^^^ polyMul _ _)]
  simp only [vdword_xor, ofVDwords, vdword_append_0, vdword_append_1, poly_0, poly_1]
  have hu := up_ushr63 h1
  rw [up] at hu
  rw [hu, BitVec.xor_zero]
  rfl

/-- What an implementation computes, for `Y` and `H` as two words each. -/
theorem mul_words (y1 y0 h1 h0 : BitVec 64) :
    (mulW y1 y0 (keyW1 h1 h0) (keyW0 h1 h0)).1 ++ (mulW y1 y0 (keyW1 h1 h0) (keyW0 h1 h0)).2 =
      Spec.Gcm.mul (y1 ++ y0) (h1 ++ h0) := by
  apply φ_inj
  rw [φ_mul, ← ρ_words, mulW_mulV, ρ_mulV, ρ_words, ← x_key h1 h0]
  ring

end VG.Proof.Gcm.Spread
