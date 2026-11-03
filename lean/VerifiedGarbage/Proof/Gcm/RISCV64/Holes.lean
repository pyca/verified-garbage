module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.ZMod.Defs
public import VerifiedGarbage.TCB.VectorCrypto
public import VerifiedGarbage.Proof.Gcm.Clmul.Arith
import Mathlib.Tactic.LinearCombination

/-!
# Carry-less products by integer multiplication with holes

Untrusted: everything here is checked by Lean. A 64-bit integer product of
two numbers whose set bits are all in one class modulo 4 (`r` and `s`),
below bit 32, has at each bit of the class `r + s` (modulo 4) the bit of
their carry-less product: the product is `2^(r+s)` times the value at 16 of
the product of their polynomials in powers of 16, whose coefficients count
at most 8 pairs, so no digit carries into the next (`testBit_mul_class`).
-/

@[expose] public section

namespace VG.Proof.Gcm.RISCV64.Holes

open Polynomial

/-! ## Digits in base 16 -/

/-- The digits of a polynomial over `ℕ` with coefficients below 16, at 16. -/
theorem eval16_digit (Q : ℕ[X]) (hQ : ∀ n, Q.coeff n < 16) (d : ℕ) :
    Q.eval 16 / 16 ^ d % 16 = Q.coeff d := by
  induction d generalizing Q with
  | zero =>
    have h := divX_mul_X_add Q
    have hc := hQ 0
    rw [← h]
    simp only [eval_add, eval_mul, eval_X, eval_C, pow_zero, Nat.div_one, coeff_add, coeff_C_zero,
      mul_coeff_zero, coeff_X_zero, mul_zero, zero_add]
    omega
  | succ d ih =>
    have hc := hQ 0
    have he : Q.eval 16 = (divX Q).eval 16 * 16 + Q.coeff 0 := by
      conv_lhs => rw [← divX_mul_X_add Q]
      simp only [eval_add, eval_mul, eval_X, eval_C]
    have ih' := ih (divX Q) (fun n => by rw [coeff_divX]; exact hQ (n + 1))
    rw [coeff_divX] at ih'
    rw [← ih', he, pow_succ', ← Nat.div_div_eq_div_mul]
    congr 2
    omega

theorem div_pow_mod16 (m q : ℕ) (hq : q < 4) : m / 2 ^ q % 2 = m % 16 / 2 ^ q % 2 := by
  interval_cases q <;> simp only [pow_zero, pow_one, Nat.reducePow] <;> omega

/-- Bit `4u + q` of a number whose digit `u` in base 16 is `c`. -/
theorem testBit_digit (n u q c : ℕ) (hq : q < 4) (h : n / 16 ^ u % 16 = c) :
    n.testBit (4 * u + q) = decide (c / 2 ^ q % 2 = 1) := by
  have e : n / 2 ^ (4 * u + q) = n / 16 ^ u / 2 ^ q := by
    rw [pow_add, pow_mul, Nat.div_div_eq_div_mul]; norm_num
  rw [Nat.testBit_eq_decide_div_mod_eq, e, div_pow_mod16 _ _ hq, h]

/-! ## Numbers with their bits in one class -/

/-- Every set bit of `x` is below `w` and congruent to `r` modulo 4. -/
def Cls (x : BitVec 64) (r w : ℕ) : Prop := ∀ i, x.getLsbD i = true → i % 4 = r ∧ i < w

/-- The bits `4u + r` of `x`, for `u < 8`, as the coefficients of a polynomial over `ℕ`. -/
noncomputable def cp (x : BitVec 64) (r : ℕ) : ℕ[X] :=
  ∑ u ∈ Finset.range 8, C (x.getLsbD (4 * u + r)).toNat * X ^ u

theorem coeff_cp (x : BitVec 64) (r u : ℕ) :
    (cp x r).coeff u = if u < 8 then (x.getLsbD (4 * u + r)).toNat else 0 := by
  simp only [cp, finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases hu : u < 8
  · rw [Finset.sum_eq_single u (fun b _ hb => by simp [Ne.symm hb])
      (fun h => absurd (Finset.mem_range.2 hu) h)]
    simp [hu]
  · rw [Finset.sum_eq_zero fun b hb => by
      have := Finset.mem_range.1 hb
      simp [show u ≠ b by omega]]
    simp [hu]

theorem coeff_cp_le (x : BitVec 64) (r u : ℕ) : (cp x r).coeff u ≤ 1 := by
  rw [coeff_cp]; split_ifs
  · exact Bool.toNat_le _
  · exact Nat.zero_le _

theorem toNat_cls {x : BitVec 64} {r : ℕ} (hr : r < 4) (hx : Cls x r 32) :
    x.toNat = 2 ^ r * (cp x r).eval 16 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [BitVec.testBit_toNat, Nat.testBit_two_pow_mul]
  by_cases hi : r ≤ i
  · obtain ⟨u, q, hq, rfl⟩ : ∃ u q, q < 4 ∧ i = 4 * u + q + r := ⟨(i - r) / 4, (i - r) % 4, by omega, by omega⟩
    rw [show 4 * u + q + r - r = 4 * u + q by omega,
      testBit_digit _ u q _ hq (eval16_digit _ (fun n => by have := coeff_cp_le x r n; omega) u), coeff_cp]
    simp only [show r ≤ 4 * u + q + r by omega, decide_true, Bool.true_and]
    by_cases hb : x.getLsbD (4 * u + q + r) = true
    · obtain ⟨h1, h2⟩ := hx _ hb
      have hq0 : q = 0 := by omega
      subst hq0
      simp only [Nat.add_zero] at hb ⊢
      simp only [show u < 8 by omega, ↓reduceIte, hb]; rfl
    · rw [Bool.not_eq_true] at hb
      rw [hb]
      split_ifs with hu
      · rcases Nat.lt_or_ge 0 q with h | h
        · cases x.getLsbD (4 * u + r) <;> simp [Bool.toNat] <;> interval_cases q <;> decide
        · have : q = 0 := by omega
          subst this; simp_all
      · simp
  · rw [decide_eq_false hi, Bool.false_and]
    by_contra hb
    rw [Bool.not_eq_false] at hb
    have := (hx i hb).1
    omega

theorem toNat_lt_cls {x : BitVec 64} {r : ℕ} (hx : Cls x r 32) : x.toNat < 2 ^ 32 :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    by_contra h
    rw [Bool.not_eq_false, BitVec.testBit_toNat] at h
    have := (hx i h).2
    omega

/-- A coefficient of the product counts at most 8 pairs. -/
theorem coeff_mul_cp_le (x y : BitVec 64) (r s d : ℕ) : (cp x r * cp y s).coeff d ≤ 8 := by
  rw [cp, Finset.sum_mul, finsetSum_coeff]
  refine (Finset.sum_le_card_nsmul _ _ 1 fun u _ => ?_).trans (by simp)
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  have h1 := Bool.toNat_le (x.getLsbD (4 * u + r))
  split_ifs
  · have h2 := coeff_cp_le y s (d - u)
    exact (Nat.mul_le_mul h1 h2).trans (by norm_num)
  · simp

/-- Bit `4d + r + s` of the integer product is the parity of coefficient `d`. -/
theorem getLsbD_mul_cls {x y : BitVec 64} {r s : ℕ} (hr : r < 4) (hs : s < 4) (hx : Cls x r 32)
    (hy : Cls y s 32) (d : ℕ) :
    (x * y).getLsbD (4 * d + (r + s)) = decide ((cp x r * cp y s).coeff d % 2 = 1) := by
  have hm : x.toNat * y.toNat < 2 ^ 64 := by
    have := Nat.mul_lt_mul'' (toNat_lt_cls hx) (toNat_lt_cls hy)
    rw [← pow_add] at this; exact this
  rw [← BitVec.testBit_toNat, BitVec.toNat_mul, Nat.mod_eq_of_lt hm, toNat_cls hr hx, toNat_cls hs hy,
    show 2 ^ r * (cp x r).eval 16 * (2 ^ s * (cp y s).eval 16) =
      2 ^ (r + s) * (cp x r * cp y s).eval 16 by rw [eval_mul, pow_add]; ring,
    Nat.testBit_two_pow_mul, decide_eq_true (by omega), Bool.true_and,
    show 4 * d + (r + s) - (r + s) = 4 * d + 0 by omega,
    testBit_digit _ d 0 _ (by omega) (eval16_digit _ (fun n => by
      have := coeff_mul_cp_le x y r s n; omega) d)]
  simp

/-! ## Polynomials over GF(2), least significant bit first -/

/-- The element of GF(2) of a bit. -/
def lbit (b : Bool) : ZMod 2 := if b then 1 else 0

/-- The polynomial of the bits of `v`, bit `i` (from the least significant) the coefficient of `Xⁱ`. -/
noncomputable def lp {n : ℕ} (v : BitVec n) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range n, C (lbit (v.getLsbD i)) * X ^ i

theorem coeff_lp {n : ℕ} (v : BitVec n) (k : ℕ) : (lp v).coeff k = lbit (v.getLsbD k) := by
  simp only [lp, finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases hk : k < n
  · rw [Finset.sum_eq_single k (fun b _ hb => by simp [Ne.symm hb])
      (fun h => absurd (Finset.mem_range.2 hk) h)]
    simp
  · rw [Finset.sum_eq_zero fun b hb => by
      have := Finset.mem_range.1 hb
      simp [show k ≠ b by omega]]
    simp [BitVec.getLsbD_of_ge v k (by omega), lbit]

theorem lbit_inj {a b : Bool} (h : lbit a = lbit b) : a = b := by
  revert h; cases a <;> cases b <;> decide

theorem lbit_xor (a b : Bool) : lbit (a ^^ b) = lbit a + lbit b := by
  cases a <;> cases b <;> decide

theorem lp_ext {n : ℕ} {a b : BitVec n} (h : lp a = lp b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  have := congrArg (coeff · i) h
  simp only [coeff_lp] at this
  exact lbit_inj this

theorem lp_xor {n : ℕ} (a b : BitVec n) : lp (a ^^^ b) = lp a + lp b := by
  ext k
  simp only [coeff_add, coeff_lp, BitVec.getLsbD_xor, lbit_xor]

theorem lbit_parity (c : ℕ) : lbit (decide (c % 2 = 1)) = (c : ZMod 2) := by
  conv_rhs => rw [← Nat.mod_add_div c 2]
  rw [Nat.cast_add, Nat.cast_mul, show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_mul, add_zero]
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> rw [h] <;> decide

/-- A number of class `r` is `Xʳ` times its class polynomial in `X⁴`. -/
theorem lp_cls {x : BitVec 64} {r : ℕ} (hr : r < 4) (hx : Cls x r 32) :
    lp x = X ^ r * expand (ZMod 2) 4 ((cp x r).map (Nat.castRingHom (ZMod 2))) := by
  ext k
  rw [coeff_lp, coeff_X_pow_mul', coeff_expand (by norm_num)]
  split_ifs with h1 h2
  · rw [coeff_map, coeff_cp]
    obtain ⟨u, hu⟩ := h2
    rw [show (k - r) / 4 = u by omega, show 4 * u + r = k by omega]
    split_ifs with h3
    · cases x.getLsbD k <;> rfl
    · rw [show x.getLsbD k = false by
        by_contra hb; rw [Bool.not_eq_false] at hb; have := (hx k hb).2; omega]
      simp [lbit]
  · rw [show x.getLsbD k = false by
      by_contra hb; rw [Bool.not_eq_false] at hb; have := (hx k hb).1; omega]
    rfl
  · rw [show x.getLsbD k = false by
      by_contra hb; rw [Bool.not_eq_false] at hb; have := (hx k hb).1; omega]
    rfl

theorem lp_mul_cls {x y : BitVec 64} {r s : ℕ} (hr : r < 4) (hs : s < 4) (hx : Cls x r 32) (hy : Cls y s 32) :
    lp x * lp y = X ^ (r + s) * expand (ZMod 2) 4 ((cp x r * cp y s).map (Nat.castRingHom (ZMod 2))) := by
  rw [lp_cls hr hx, lp_cls hs hy, Polynomial.map_mul, map_mul, pow_add]
  ring

/-- The integer product's bits of the class `r + s` are the carry-less product's. -/
theorem lbit_mul_cls {x y : BitVec 64} {r s : ℕ} (hr : r < 4) (hs : s < 4) (hx : Cls x r 32)
    (hy : Cls y s 32) {k : ℕ} (hk : k % 4 = (r + s) % 4) :
    lbit ((x * y).getLsbD k) = (lp x * lp y).coeff k := by
  rw [lp_mul_cls hr hs hx hy, coeff_X_pow_mul']
  split_ifs with h
  · obtain ⟨d, rfl⟩ : ∃ d, k = 4 * d + (r + s) := ⟨(k - (r + s)) / 4, by omega⟩
    have hdv : 4 ∣ 4 * d + (r + s) - (r + s) := ⟨d, by omega⟩
    rw [coeff_expand (by norm_num)]
    simp only [hdv, ↓reduceIte]
    rw [coeff_map, getLsbD_mul_cls hr hs hx hy,
      show (4 * d + (r + s) - (r + s)) / 4 = d by omega, lbit_parity]
    rfl
  · have hm : x.toNat * y.toNat < 2 ^ 64 := by
      have := Nat.mul_lt_mul'' (toNat_lt_cls hx) (toNat_lt_cls hy)
      rw [← pow_add] at this; exact this
    rw [← BitVec.testBit_toNat, BitVec.toNat_mul, Nat.mod_eq_of_lt hm, toNat_cls hr hx, toNat_cls hs hy,
      show 2 ^ r * (cp x r).eval 16 * (2 ^ s * (cp y s).eval 16) =
        2 ^ (r + s) * ((cp x r).eval 16 * (cp y s).eval 16) by rw [pow_add]; ring,
      Nat.testBit_two_pow_mul, decide_eq_false h, Bool.false_and]
    rfl

/-- The carry-less product has no bits outside the class `r + s`. -/
theorem coeff_mul_cls_ne {x y : BitVec 64} {r s : ℕ} (hr : r < 4) (hs : s < 4) (hx : Cls x r 32)
    (hy : Cls y s 32) {k : ℕ} (hk : k % 4 ≠ (r + s) % 4) : (lp x * lp y).coeff k = 0 := by
  rw [lp_mul_cls hr hs hx hy, coeff_X_pow_mul']
  split_ifs with h
  · have hdv : ¬ 4 ∣ k - (r + s) := by rintro ⟨d, hd⟩; omega
    rw [coeff_expand (by norm_num)]
    simp only [hdv, ↓reduceIte]
  · rfl

/-! ## `polyMul` -/

theorem lp_shl (b : BitVec 64) {i : ℕ} (hi : i < 64) : lp ((b.setWidth 128) <<< i) = X ^ i * lp b := by
  ext k
  rw [coeff_lp, coeff_X_pow_mul', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  split_ifs with h
  · rw [coeff_lp]
    by_cases hk : k < 128
    · simp only [hk, decide_true, Bool.true_and, show ¬ k < i by omega, decide_false, Bool.not_false]
      by_cases hb : k - i < 128
      · simp [hb]
      · simp [hb, BitVec.getLsbD_of_ge b (k - i) (by omega)]
    · simp [hk, BitVec.getLsbD_of_ge b (k - i) (by omega), lbit]
  · simp [show k < i by omega, lbit]

/-- The carry-less product as polynomials, least significant bit first. -/
theorem lp_polyMul (a b : BitVec 64) : lp (VG.VectorCrypto.polyMul a b) = lp a * lp b := by
  have key : ∀ k ≤ 64, lp ((List.range k).foldl (fun acc i =>
      if a.getLsbD i then acc ^^^ (b.setWidth 128 <<< i) else acc) 0) =
      (∑ i ∈ Finset.range k, C (lbit (a.getLsbD i)) * X ^ i) * lp b := by
    intro k hk
    induction k with
    | zero =>
      ext n; simp [coeff_lp, lbit]
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Finset.sum_range_succ,
        add_mul, ← ih (by omega)]
      split_ifs with h
      · rw [lp_xor, lp_shl b (by omega), h]; simp [lbit]
      · rw [Bool.not_eq_true] at h; rw [h]; simp [lbit]
  rw [VG.VectorCrypto.polyMul, key 64 le_rfl]
  rfl

/-! ## The masks -/

/-- The bits congruent to `i` modulo 4. -/
def K (i : ℕ) : BitVec 64 := 0x1111111111111111#64 <<< i

theorem getLsbD_K {i : ℕ} (hi : i < 4) {j : ℕ} (hj : j < 64) : (K i).getLsbD j = decide (j % 4 = i) := by
  revert j
  interval_cases i <;> decide

theorem cls_K {a : BitVec 64} (ha : a.toNat < 2 ^ 32) {i : ℕ} (hi : i < 4) : Cls (a &&& K i) i 32 := by
  intro j hj
  rw [BitVec.getLsbD_and, Bool.and_eq_true] at hj
  obtain ⟨h1, h2⟩ := hj
  have hj32 : j < 32 := by
    by_contra h
    rw [← BitVec.testBit_toNat, Nat.testBit_lt_two_pow
      (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (by omega)))] at h1
    exact Bool.false_ne_true h1
  rw [getLsbD_K hi (by omega)] at h2
  exact ⟨of_decide_eq_true h2, hj32⟩

theorem lp_split (a : BitVec 64) :
    lp a = lp (a &&& K 0) + lp (a &&& K 1) + lp (a &&& K 2) + lp (a &&& K 3) := by
  ext n
  simp only [coeff_add, coeff_lp, BitVec.getLsbD_and]
  by_cases hn : n < 64
  · rw [getLsbD_K (by norm_num) hn, getLsbD_K (by norm_num) hn, getLsbD_K (by norm_num) hn,
      getLsbD_K (by norm_num) hn]
    have : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
    cases a.getLsbD n <;> interval_cases h : n % 4 <;> simp [lbit]
  · simp [BitVec.getLsbD_of_ge a n (by omega), lbit]

/-- The words `zₜ` of the code: the products of the parts of `a` and `b` whose
classes add up to `t`, `b`'s parts in order. -/
def zc (a : BitVec 64) (bs : ℕ → BitVec 64) (t : ℕ) : BitVec 64 :=
  (a &&& K t) * bs 0 ^^^ (a &&& K ((t + 3) % 4)) * bs 1 ^^^ (a &&& K ((t + 2) % 4)) * bs 2 ^^^
    (a &&& K ((t + 1) % 4)) * bs 3

/-- The class `t` of each `zₜ`, together. -/
def holes (a : BitVec 64) (bs : ℕ → BitVec 64) : BitVec 64 :=
  (zc a bs 0 &&& K 0) ||| (zc a bs 1 &&& K 1) ||| (zc a bs 2 &&& K 2) ||| (zc a bs 3 &&& K 3)

/-- The carry-less product of two 32-bit values by multiplications with holes. -/
theorem holes_eq (a b : BitVec 64) (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    holes a (fun j => b &&& K j) = (VG.VectorCrypto.polyMul a b).setWidth 64 := by
  apply lp_ext
  ext k
  rw [coeff_lp (holes _ _) k, coeff_lp (BitVec.setWidth 64 _) k, BitVec.getLsbD_setWidth]
  by_cases hk : k < 64
  · rw [decide_eq_true hk, Bool.true_and, ← coeff_lp (VG.VectorCrypto.polyMul a b) k, lp_polyMul,
      lp_split a, lp_split b]
    have c : ∀ i j, i < 4 → j < 4 → (i + j) % 4 = k % 4 →
        lbit (((a &&& K i) * (b &&& K j)).getLsbD k) = (lp (a &&& K i) * lp (b &&& K j)).coeff k :=
      fun i j hi hj h => lbit_mul_cls hi hj (cls_K ha hi) (cls_K hb hj) h.symm
    have z : ∀ i j, i < 4 → j < 4 → (i + j) % 4 ≠ k % 4 → (lp (a &&& K i) * lp (b &&& K j)).coeff k = 0 :=
      fun i j hi hj h => coeff_mul_cls_ne hi hj (cls_K ha hi) (cls_K hb hj) (Ne.symm h)
    simp (disch := omega) only [holes, zc, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor,
      getLsbD_K, add_mul, mul_add, coeff_add]
    have : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases h : k % 4 <;> simp only [Nat.reduceEqDiff, decide_true, decide_false, Bool.and_true,
      Bool.and_false, Bool.or_false, Bool.false_or, lbit_xor]
    · rw [c 0 0 (by norm_num) (by norm_num) (by omega), c 3 1 (by norm_num) (by norm_num) (by omega), c 2 2 (by norm_num) (by norm_num) (by omega), c 1 3 (by norm_num) (by norm_num) (by omega)]
      linear_combination -(z 1 0 (by norm_num) (by norm_num) (by omega)
        + z 2 0 (by norm_num) (by norm_num) (by omega)
        + z 3 0 (by norm_num) (by norm_num) (by omega)
        + z 0 1 (by norm_num) (by norm_num) (by omega)
        + z 1 1 (by norm_num) (by norm_num) (by omega)
        + z 2 1 (by norm_num) (by norm_num) (by omega)
        + z 0 2 (by norm_num) (by norm_num) (by omega)
        + z 1 2 (by norm_num) (by norm_num) (by omega)
        + z 3 2 (by norm_num) (by norm_num) (by omega)
        + z 0 3 (by norm_num) (by norm_num) (by omega)
        + z 2 3 (by norm_num) (by norm_num) (by omega)
        + z 3 3 (by norm_num) (by norm_num) (by omega))
    · rw [c 1 0 (by norm_num) (by norm_num) (by omega), c 0 1 (by norm_num) (by norm_num) (by omega), c 3 2 (by norm_num) (by norm_num) (by omega), c 2 3 (by norm_num) (by norm_num) (by omega)]
      linear_combination -(z 0 0 (by norm_num) (by norm_num) (by omega)
        + z 2 0 (by norm_num) (by norm_num) (by omega)
        + z 3 0 (by norm_num) (by norm_num) (by omega)
        + z 1 1 (by norm_num) (by norm_num) (by omega)
        + z 2 1 (by norm_num) (by norm_num) (by omega)
        + z 3 1 (by norm_num) (by norm_num) (by omega)
        + z 0 2 (by norm_num) (by norm_num) (by omega)
        + z 1 2 (by norm_num) (by norm_num) (by omega)
        + z 2 2 (by norm_num) (by norm_num) (by omega)
        + z 0 3 (by norm_num) (by norm_num) (by omega)
        + z 1 3 (by norm_num) (by norm_num) (by omega)
        + z 3 3 (by norm_num) (by norm_num) (by omega))
    · rw [c 2 0 (by norm_num) (by norm_num) (by omega), c 1 1 (by norm_num) (by norm_num) (by omega), c 0 2 (by norm_num) (by norm_num) (by omega), c 3 3 (by norm_num) (by norm_num) (by omega)]
      linear_combination -(z 0 0 (by norm_num) (by norm_num) (by omega)
        + z 1 0 (by norm_num) (by norm_num) (by omega)
        + z 3 0 (by norm_num) (by norm_num) (by omega)
        + z 0 1 (by norm_num) (by norm_num) (by omega)
        + z 2 1 (by norm_num) (by norm_num) (by omega)
        + z 3 1 (by norm_num) (by norm_num) (by omega)
        + z 1 2 (by norm_num) (by norm_num) (by omega)
        + z 2 2 (by norm_num) (by norm_num) (by omega)
        + z 3 2 (by norm_num) (by norm_num) (by omega)
        + z 0 3 (by norm_num) (by norm_num) (by omega)
        + z 1 3 (by norm_num) (by norm_num) (by omega)
        + z 2 3 (by norm_num) (by norm_num) (by omega))
    · rw [c 3 0 (by norm_num) (by norm_num) (by omega), c 2 1 (by norm_num) (by norm_num) (by omega), c 1 2 (by norm_num) (by norm_num) (by omega), c 0 3 (by norm_num) (by norm_num) (by omega)]
      linear_combination -(z 0 0 (by norm_num) (by norm_num) (by omega)
        + z 1 0 (by norm_num) (by norm_num) (by omega)
        + z 2 0 (by norm_num) (by norm_num) (by omega)
        + z 0 1 (by norm_num) (by norm_num) (by omega)
        + z 1 1 (by norm_num) (by norm_num) (by omega)
        + z 3 1 (by norm_num) (by norm_num) (by omega)
        + z 0 2 (by norm_num) (by norm_num) (by omega)
        + z 2 2 (by norm_num) (by norm_num) (by omega)
        + z 3 2 (by norm_num) (by norm_num) (by omega)
        + z 1 3 (by norm_num) (by norm_num) (by omega)
        + z 2 3 (by norm_num) (by norm_num) (by omega)
        + z 3 3 (by norm_num) (by norm_num) (by omega))
  · simp [hk, BitVec.getLsbD_of_ge _ k (by omega : 64 ≤ k)]

/-! ## 64 × 64 bits by Karatsuba -/

theorem lp_append {n m : ℕ} (a : BitVec n) (b : BitVec m) : lp (a ++ b) = lp b + X ^ m * lp a := by
  ext k
  rw [coeff_add, coeff_X_pow_mul', coeff_lp, coeff_lp, BitVec.getLsbD_append]
  by_cases h1 : k < m
  · simp [h1, show ¬ m ≤ k by omega]
  · simp only [h1, ↓reduceIte, show m ≤ k by omega, coeff_lp, BitVec.getLsbD_of_ge b k (by omega)]
    simp [lbit]

/-- The low half of a word. -/
def lo32 (x : BitVec 64) : BitVec 64 := (x <<< 32) >>> 32
/-- The high half of a word. -/
def hi32 (x : BitVec 64) : BitVec 64 := x >>> 32

theorem getLsbD_lo32 (x : BitVec 64) (k : ℕ) : (lo32 x).getLsbD k = (decide (k < 32) && x.getLsbD k) := by
  simp only [lo32, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  by_cases h : k < 32
  · simp [h, show 32 + k < 64 by omega]
  · simp [h, show ¬ 32 + k < 64 by omega]

theorem getLsbD_hi32 (x : BitVec 64) (k : ℕ) : (hi32 x).getLsbD k = x.getLsbD (k + 32) := by
  simp [hi32, BitVec.getLsbD_ushiftRight, Nat.add_comm]

theorem toNat_lt_of_getLsbD {x : BitVec 64} (h : ∀ k, 32 ≤ k → x.getLsbD k = false) : x.toNat < 2 ^ 32 :=
  Nat.lt_pow_two_of_testBit _ fun k hk => by rw [BitVec.testBit_toNat]; exact h k hk

theorem lo32_lt (x : BitVec 64) : (lo32 x).toNat < 2 ^ 32 :=
  toNat_lt_of_getLsbD fun k hk => by rw [getLsbD_lo32]; simp [show ¬ k < 32 by omega]

theorem hi32_lt (x : BitVec 64) : (hi32 x).toNat < 2 ^ 32 :=
  toNat_lt_of_getLsbD fun k hk => by rw [getLsbD_hi32]; exact BitVec.getLsbD_of_ge x _ (by omega)

theorem xor_lt {x y : BitVec 64} (hx : x.toNat < 2 ^ 32) (hy : y.toNat < 2 ^ 32) : (x ^^^ y).toNat < 2 ^ 32 := by
  rw [BitVec.toNat_xor]; exact Nat.xor_lt_two_pow hx hy

theorem lp_lo_hi (x : BitVec 64) : lp x = lp (lo32 x) + X ^ 32 * lp (hi32 x) := by
  ext k
  rw [coeff_add, coeff_X_pow_mul', coeff_lp, coeff_lp, getLsbD_lo32]
  split_ifs with h
  · rw [coeff_lp, getLsbD_hi32, show k - 32 + 32 = k by omega]; simp [show ¬ k < 32 by omega, lbit]
  · simp [show k < 32 by omega]

theorem lp_shl32 (x : BitVec 64) : lp (x <<< 32) = X ^ 32 * lp (lo32 x) := by
  ext k
  rw [coeff_X_pow_mul', coeff_lp, BitVec.getLsbD_shiftLeft]
  split_ifs with h
  · rw [coeff_lp, getLsbD_lo32]
    by_cases hk : k < 64
    · simp [hk, show ¬ k < 32 by omega, show k - 32 < 32 by omega]
    · simp [hk, show ¬ k - 32 < 32 by omega, lbit]
  · simp [show k < 32 by omega, lbit]

/-- The low word of a product of 32-bit values is all of it. -/
theorem coeff_mul_lt32 {a b : BitVec 64} (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) {k : ℕ} (hk : 63 ≤ k) :
    (lp a * lp b).coeff k = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  have bit0 : ∀ {c : BitVec 64}, c.toNat < 2 ^ 32 → ∀ i, 32 ≤ i → (lp c).coeff i = 0 := fun hc i hi => by
    rw [coeff_lp, ← BitVec.testBit_toNat,
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hi))]; rfl
  rcases Nat.lt_or_ge ij.1 32 with h | h
  · rw [bit0 hb ij.2 (by omega), mul_zero]
  · rw [bit0 ha ij.1 h, zero_mul]

theorem lp_holes {a b : BitVec 64} (ha : a.toNat < 2 ^ 32) (hb : b.toNat < 2 ^ 32) :
    lp (holes a fun j => b &&& K j) = lp a * lp b := by
  rw [holes_eq a b ha hb]
  ext k
  rw [coeff_lp, BitVec.getLsbD_setWidth]
  by_cases hk : k < 64
  · rw [decide_eq_true hk, Bool.true_and, ← coeff_lp, lp_polyMul]
  · rw [decide_eq_false hk, Bool.false_and, coeff_mul_lt32 ha hb (by omega)]; rfl

/-- The 64-bit carry-less product, by three 32-bit ones: the low halves' product, -/
def pmL (x y : BitVec 64) : BitVec 64 := holes (lo32 x) fun j => lo32 y &&& K j
/-- the high halves', -/
def pmH (x y : BitVec 64) : BitVec 64 := holes (hi32 x) fun j => hi32 y &&& K j
/-- the middle term, -/
def pmM (x y : BitVec 64) : BitVec 64 :=
  (holes (lo32 x ^^^ hi32 x) fun j => (lo32 y ^^^ hi32 y) &&& K j) ^^^ pmL x y ^^^ pmH x y
/-- and its low and high words. -/
def pm (x y : BitVec 64) : BitVec 64 × BitVec 64 :=
  (pmL x y ^^^ pmM x y <<< 32, pmH x y ^^^ pmM x y >>> 32)

theorem two_P : (2 : (ZMod 2)[X]) = 0 := by
  rw [← map_ofNat C 2, show (OfNat.ofNat 2 : ZMod 2) = 0 from rfl, map_zero]

theorem pm_eq (x y : BitVec 64) : (pm x y).2 ++ (pm x y).1 = VG.VectorCrypto.polyMul x y := by
  apply lp_ext
  have hx := lo32_lt x; have hx' := hi32_lt x; have hy := lo32_lt y; have hy' := hi32_lt y
  have eL : lp (pmL x y) = lp (lo32 x) * lp (lo32 y) := lp_holes hx hy
  have eH : lp (pmH x y) = lp (hi32 x) * lp (hi32 y) := lp_holes hx' hy'
  have eM : lp (pmM x y) = (lp (lo32 x) + lp (hi32 x)) * (lp (lo32 y) + lp (hi32 y)) +
      lp (lo32 x) * lp (lo32 y) + lp (hi32 x) * lp (hi32 y) := by
    rw [pmM, lp_xor, lp_xor, lp_holes (xor_lt hx hx') (xor_lt hy hy'), eL, eH, lp_xor, lp_xor]
  have h1 := lp_lo_hi (pmM x y)
  have e1 : lp (pm x y).1 = lp (pmL x y) + X ^ 32 * lp (lo32 (pmM x y)) := by
    rw [pm, lp_xor, lp_shl32]
  have e2 : lp (pm x y).2 = lp (pmH x y) + lp (hi32 (pmM x y)) := by
    rw [pm, lp_xor]; rfl
  rw [lp_append, lp_polyMul, lp_lo_hi x, lp_lo_hi y, e1, e2, eL, eH]
  linear_combination (-X ^ 32 : (ZMod 2)[X]) * h1 + X ^ 32 * eM +
    X ^ 32 * (lp (lo32 x) * lp (lo32 y) + lp (hi32 x) * lp (hi32 y)) * two_P

/-! ## GHASH from the 64-bit products

As in `Proof/Gcm/X86_64/Ghash.lean`, in the ring `Q` of `Proof/Gcm/Poly.lean`: a
block is two words, the first its terms of degrees below 64 (`φ_append`). -/

section Ghash
open VG.Proof.Gcm.Poly VG.Proof.Gcm.Clmul

/-- A word product: `pm`'s high word holds the low degrees. -/
theorem ψ_pm (a b : BitVec 64) : ψ (pm a b).2 + x ^ 64 * ψ (pm a b).1 = x * ψ a * ψ b := by
  rw [← φ_append, pm_eq]
  simp only [φ, ψ, gp_polyMul, map_mul, AdjoinRoot.mk_X]

theorem gp_shr_shl (w : BitVec 64) {s : Nat} (hs : 0 < s) (hs' : s < 64) :
    gp (w >>> s) + X ^ 64 * gp (w <<< (64 - s)) = X ^ s * gp w := by
  ext d
  rw [coeff_add, coeff_gp, coeff_X_pow_mul', coeff_X_pow_mul', coeff_gp, coeff_gp,
    BitVec.getMsbD_ushiftRight, BitVec.getMsbD_shiftLeft]
  by_cases h1 : s ≤ d
  · by_cases h2 : 64 ≤ d
    · simp only [h1, h2, ↓reduceIte, decide_eq_false (show ¬ d < 64 by omega), Bool.false_and,
        show d - 64 + (64 - s) = d - s by omega]
      simp only [bit, Bool.false_eq_true, ↓reduceIte, zero_add]
    · simp only [h1, h2, ↓reduceIte, decide_eq_true (show d < 64 by omega),
        decide_eq_false (show ¬ d < s by omega), Bool.not_false, Bool.true_and, add_zero]
  · simp only [h1, show ¬ 64 ≤ d by omega, ↓reduceIte,
      decide_eq_true (show d < s by omega), Bool.not_true, Bool.false_and, Bool.and_false, add_zero]
    rfl

theorem ψ_shr_shl (w : BitVec 64) {s : Nat} (hs : 0 < s) (hs' : s < 64) :
    ψ (w >>> s) + x ^ 64 * ψ (w <<< (64 - s)) = x ^ s * ψ w := by
  have := congrArg (AdjoinRoot.mk g) (gp_shr_shl w hs hs')
  simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_X] at this
  exact this

/-- What a fold adds to the lower word, -/
def foldLo (lo w : BitVec 64) : BitVec 64 := (((lo ^^^ w) ^^^ (w >>> 1)) ^^^ (w >>> 2)) ^^^ (w >>> 7)

/-- and to the higher. -/
def foldHi (hi w : BitVec 64) : BitVec 64 := ((hi ^^^ (w <<< 63)) ^^^ (w <<< 62)) ^^^ (w <<< 57)

theorem ψ_fold (lo hi w : BitVec 64) :
    ψ (foldLo lo w) + x ^ 64 * ψ (foldHi hi w) = ψ lo + x ^ 64 * ψ hi + x ^ 128 * ψ w := by
  have e1 := ψ_shr_shl w (s := 1) (by decide) (by decide)
  have e2 := ψ_shr_shl w (s := 2) (by decide) (by decide)
  have e7 := ψ_shr_shl w (s := 7) (by decide) (by decide)
  simp only [foldLo, foldHi, ψ_xor]
  simp only [Nat.reduceSub] at e1 e2 e7
  linear_combination e1 + e2 + e7 - ψ w * x128

/-- The reduction: `W₃` into `W₁, W₂`, then `W₂` into `W₀, W₁`. -/
def reduce (w0 w1 w2 w3 : BitVec 64) : BitVec 128 :=
  foldLo w0 (foldHi w2 w3) ++ foldHi (foldLo w1 w3) (foldHi w2 w3)

theorem φ_reduce (w0 w1 w2 w3 : BitVec 64) :
    φ (reduce w0 w1 w2 w3) = ψ w0 + x ^ 64 * ψ w1 + x ^ 128 * ψ w2 + x ^ 192 * ψ w3 := by
  rw [reduce, φ_append, ψ_fold]
  have := ψ_fold w1 w2 w3
  linear_combination x ^ 64 * this

/-- The key's first word, `H · x⁻¹`: `H` shifted up a bit, `x⁻¹ = 1 + x + x⁶ + x¹²⁷` added if
its constant term was set. -/
def key0 (h0 h1 : BitVec 64) : BitVec 64 :=
  ((h0 <<< 1) ^^^ (h1 >>> 63)) ^^^ ((0#64 - (h0 >>> 63)) &&& VG.Impl.Gcm.Clmul.poly)

/-- … and its second. -/
def key1 (h0 h1 : BitVec 64) : BitVec 64 := (h1 <<< 1) ^^^ ((0#64 - (h0 >>> 63)) &&& 1#64)

theorem mask_msb (h c : BitVec 64) : (0#64 - (h >>> 63)) &&& c = if h.getMsbD 0 then c else 0#64 := by
  rw [ushr63]; split_ifs
  · rw [show 0#64 - 1#64 = BitVec.allOnes 64 by decide, BitVec.allOnes_and]
  · simp

theorem ψ_one64 : ψ (1#64) = x ^ 63 := by
  simp only [ψ, gp_one64, map_pow, AdjoinRoot.mk_X]

theorem ψ_zero64 : ψ (0#64) = 0 := by simp only [ψ, gp_zero', map_zero]

theorem x_φ_key (h0 h1 : BitVec 64) : x * φ (key0 h0 h1 ++ key1 h0 h1) = φ (h0 ++ h1) := by
  rw [φ_append, φ_append, key0, key1, mask_msb, mask_msb]
  simp only [ψ_xor]
  rw [ψ_ushr63, ψ_shl1 h0, ψ_shl1 h1]
  cases hb0 : h0.getMsbD 0 <;> cases hb1 : h1.getMsbD 0 <;>
    simp only [Bool.false_eq_true, ↓reduceIte, ψ_zero64, ψ_poly, ψ_one64]
  · ring
  · ring
  · linear_combination x128 + (x + x ^ 2 + x ^ 7) * two_Q
  · linear_combination x128 + (x + x ^ 2 + x ^ 7) * two_Q

/-- One block's product by the key `k` (`key0`, `key1`), as the code computes it. -/
def mulK (y0 y1 k0 k1 : BitVec 64) : BitVec 128 :=
  let l := pm y0 k0
  let h := pm y1 k1
  let m := pm (y0 ^^^ y1) (k0 ^^^ k1)
  reduce l.2 (l.1 ^^^ (m.2 ^^^ l.2 ^^^ h.2)) ((m.1 ^^^ l.1 ^^^ h.1) ^^^ h.2) h.1

theorem φ_mulK (y0 y1 k0 k1 : BitVec 64) : φ (mulK y0 y1 k0 k1) = x * φ (y0 ++ y1) * φ (k0 ++ k1) := by
  have eL := ψ_pm y0 k0
  have eH := ψ_pm y1 k1
  have eM := ψ_pm (y0 ^^^ y1) (k0 ^^^ k1)
  simp only [ψ_xor] at eM
  rw [mulK, φ_reduce, φ_append, φ_append]
  simp only [ψ_xor]
  linear_combination eL + x ^ 64 * (eM + eL + eH) + x ^ 128 * eH +
    x ^ 65 * (ψ y0 * ψ k0 + ψ y1 * ψ k1) * two_Q

/-- The block product of SP 800-38D. -/
theorem mulK_eq (y0 y1 h0 h1 : BitVec 64) :
    mulK y0 y1 (key0 h0 h1) (key1 h0 h1) = Spec.Gcm.mul (y0 ++ y1) (h0 ++ h1) := by
  apply φ_inj
  rw [φ_mulK, φ_mul, ← x_φ_key h0 h1]
  ring

end Ghash

end VG.Proof.Gcm.RISCV64.Holes
