module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.ZMod.Defs
public import VerifiedGarbage.Proof.Gcm.Holes
import Mathlib.Tactic.LinearCombination
import VerifiedGarbage.Proof.Framework.Omega

-- separate module: the mathematics is of no instruction set (as `Proof/Gcm/Holes.lean`), and a module of a
-- target may not be imported by another target's.

/-!
# GHASH by 32-bit integer multiplications with holes

Untrusted: everything here is checked by Lean. The mathematics of an
implementation that computes the carry-less products of GHASH with an
integer multiplication that gives only the low 32 bits of a product
(`Impl/Gcm/Arm.lean`), for any instruction set.

* A 16-bit value is split into its three classes of bits modulo 3, and each
  class of a 32-bit carry-less product is the sum of the three integer
  products of classes adding up to it: the two factors of a product have at
  most 6 bits each, so at most 6 pairs of bits reach a bit of the product,
  and no carry reaches the next bit of the class, three bits up (`h3`,
  `lp_h3`). The products of 16-bit values are below `2³²`.
* A 32-bit product is three of those (Karatsuba: `m32`, `lp_m32`), a 64-bit
  one three of those (`m64`, `lp_m64`), and a block's three of those, whose
  256 bits are reduced modulo `g` with shifts (`fin`, `φ_fin`).
* The key is `H · x⁻¹` (`keyW`, `x_φ_keyW`): the products are those of
  polynomials times `x`, as the bits of a block are in the reverse order of
  an integer's (`gp_of_lp`).
* So a block's product by the key is SP 800-38D's (`mulW`, `mulW_eq`).
-/

@[expose] public section

namespace VG.Proof.Gcm.Holes16

open Polynomial
open VG.Proof.Gcm.Holes (lbit lp coeff_lp lbit_xor lp_xor lbit_parity lp_append two_P)

/-! ## Digits in base 8 -/

/-- The digits of a polynomial over `ℕ` with coefficients below 8, at 8. -/
theorem eval8_digit (Q : ℕ[X]) (hQ : ∀ n, Q.coeff n < 8) (d : ℕ) :
    Q.eval 8 / 8 ^ d % 8 = Q.coeff d := by
  induction d generalizing Q with
  | zero =>
    have h := divX_mul_X_add Q
    have hc := hQ 0
    rw [← h]
    simp only [eval_add, eval_mul, eval_X, eval_C, pow_zero, Nat.div_one, coeff_add, coeff_C_zero,
      mul_coeff_zero, coeff_X_zero, mul_zero, zero_add]
    omega_using [hc]
  | succ d ih =>
    have hc := hQ 0
    have he : Q.eval 8 = (divX Q).eval 8 * 8 + Q.coeff 0 := by
      conv_lhs => rw [← divX_mul_X_add Q]
      simp only [eval_add, eval_mul, eval_X, eval_C]
    have ih' := ih (divX Q) (fun n => by rw [coeff_divX]; exact hQ (n + 1))
    rw [coeff_divX] at ih'
    rw [← ih', he, pow_succ', ← Nat.div_div_eq_div_mul]
    congr 2
    omega_using [hc]

theorem div_pow_mod8 (m q : ℕ) (hq : q < 3) : m / 2 ^ q % 2 = m % 8 / 2 ^ q % 2 := by
  interval_cases q <;> simp only [pow_zero, pow_one, Nat.reducePow] <;> omega_using []

/-- Bit `3u + q` of a number whose digit `u` in base 8 is `c`. -/
theorem testBit_digit (n u q c : ℕ) (hq : q < 3) (h : n / 8 ^ u % 8 = c) :
    n.testBit (3 * u + q) = decide (c / 2 ^ q % 2 = 1) := by
  have e : n / 2 ^ (3 * u + q) = n / 8 ^ u / 2 ^ q := by
    rw [pow_add, pow_mul, Nat.div_div_eq_div_mul]; norm_num
  rw [Nat.testBit_eq_decide_div_mod_eq, e, div_pow_mod8 _ _ hq, h]

/-! ## Numbers with their bits in one class -/

/-- Every set bit of `x` is below `w` and congruent to `r` modulo 3. -/
def Cls (x : BitVec 32) (r w : ℕ) : Prop := ∀ i, x.getLsbD i = true → i % 3 = r ∧ i < w

/-- The bits `3u + r` of `x`, for `u < 6`, as the coefficients of a polynomial over `ℕ`. -/
noncomputable def cp (x : BitVec 32) (r : ℕ) : ℕ[X] :=
  ∑ u ∈ Finset.range 6, C (x.getLsbD (3 * u + r)).toNat * X ^ u

theorem coeff_cp (x : BitVec 32) (r u : ℕ) :
    (cp x r).coeff u = if u < 6 then (x.getLsbD (3 * u + r)).toNat else 0 := by
  simp only [cp, finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases hu : u < 6
  · rw [Finset.sum_eq_single u (fun b _ hb => by simp [Ne.symm hb])
      (fun h => absurd (Finset.mem_range.2 hu) h)]
    simp [hu]
  · rw [Finset.sum_eq_zero fun b hb => by
      have := Finset.mem_range.1 hb
      simp [show u ≠ b by omega_using [hu, this]]]
    simp [hu]

theorem coeff_cp_le (x : BitVec 32) (r u : ℕ) : (cp x r).coeff u ≤ 1 := by
  rw [coeff_cp]; split_ifs
  · exact Bool.toNat_le _
  · exact Nat.zero_le _

theorem toNat_cls {x : BitVec 32} {r : ℕ} (hr : r < 3) (hx : Cls x r 16) :
    x.toNat = 2 ^ r * (cp x r).eval 8 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [BitVec.testBit_toNat, Nat.testBit_two_pow_mul]
  by_cases hi : r ≤ i
  · obtain ⟨u, q, hq, rfl⟩ : ∃ u q, q < 3 ∧ i = 3 * u + q + r := ⟨(i - r) / 3, (i - r) % 3, by omega, by omega⟩
    rw [show 3 * u + q + r - r = 3 * u + q by omega,
      testBit_digit _ u q _ hq (eval8_digit _ (fun n => by have := coeff_cp_le x r n; omega) u), coeff_cp]
    simp only [show r ≤ 3 * u + q + r by omega, decide_true, Bool.true_and]
    by_cases hb : x.getLsbD (3 * u + q + r) = true
    · obtain ⟨h1, h2⟩ := hx _ hb
      have hq0 : q = 0 := by omega
      subst hq0
      simp only [Nat.add_zero] at hb ⊢
      simp only [show u < 6 by omega, ↓reduceIte, hb]; rfl
    · rw [Bool.not_eq_true] at hb
      rw [hb]
      split_ifs with hu
      · rcases Nat.lt_or_ge 0 q with h | h
        · cases x.getLsbD (3 * u + r) <;> simp [Bool.toNat] <;> interval_cases q <;> decide
        · have : q = 0 := by omega
          subst this; simp_all
      · simp
  · rw [decide_eq_false hi, Bool.false_and]
    by_contra hb
    rw [Bool.not_eq_false] at hb
    have := (hx i hb).1
    omega

theorem toNat_lt_cls {x : BitVec 32} {r : ℕ} (hx : Cls x r 16) : x.toNat < 2 ^ 16 :=
  Nat.lt_pow_two_of_testBit _ fun i hi => by
    by_contra h
    rw [Bool.not_eq_false, BitVec.testBit_toNat] at h
    have := (hx i h).2
    omega_using [hi, this]

/-- A coefficient of the product counts at most 6 pairs. -/
theorem coeff_mul_cp_le (x y : BitVec 32) (r s d : ℕ) : (cp x r * cp y s).coeff d ≤ 6 := by
  rw [cp, Finset.sum_mul, finsetSum_coeff]
  refine (Finset.sum_le_card_nsmul _ _ 1 fun u _ => ?_).trans (by simp)
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  have h1 := Bool.toNat_le (x.getLsbD (3 * u + r))
  split_ifs
  · have h2 := coeff_cp_le y s (d - u)
    exact (Nat.mul_le_mul h1 h2).trans (by norm_num)
  · simp

theorem mul_lt_cls {x y : BitVec 32} {r s : ℕ} (hx : Cls x r 16) (hy : Cls y s 16) :
    x.toNat * y.toNat < 2 ^ 32 := by
  have := Nat.mul_lt_mul'' (toNat_lt_cls hx) (toNat_lt_cls hy)
  rw [← pow_add] at this; exact this

/-- Bit `3d + r + s` of the integer product is the parity of coefficient `d`. -/
theorem getLsbD_mul_cls {x y : BitVec 32} {r s : ℕ} (hr : r < 3) (hs : s < 3) (hx : Cls x r 16)
    (hy : Cls y s 16) (d : ℕ) :
    (x * y).getLsbD (3 * d + (r + s)) = decide ((cp x r * cp y s).coeff d % 2 = 1) := by
  rw [← BitVec.testBit_toNat, BitVec.toNat_mul, Nat.mod_eq_of_lt (mul_lt_cls hx hy), toNat_cls hr hx,
    toNat_cls hs hy,
    show 2 ^ r * (cp x r).eval 8 * (2 ^ s * (cp y s).eval 8) =
      2 ^ (r + s) * (cp x r * cp y s).eval 8 by rw [eval_mul, pow_add]; ring,
    Nat.testBit_two_pow_mul, decide_eq_true (by omega_using []), Bool.true_and,
    show 3 * d + (r + s) - (r + s) = 3 * d + 0 by omega_using [],
    testBit_digit _ d 0 _ (by omega_using []) (eval8_digit _ (fun n => by
      have := coeff_mul_cp_le x y r s n; omega_using [this]) d)]
  simp

/-- A number of class `r` is `Xʳ` times its class polynomial in `X³`. -/
theorem lp_cls {x : BitVec 32} {r : ℕ} (hr : r < 3) (hx : Cls x r 16) :
    lp x = X ^ r * expand (ZMod 2) 3 ((cp x r).map (Nat.castRingHom (ZMod 2))) := by
  ext k
  rw [coeff_lp, coeff_X_pow_mul', coeff_expand (by norm_num)]
  split_ifs with h1 h2
  · rw [coeff_map, coeff_cp]
    obtain ⟨u, hu⟩ := h2
    rw [show (k - r) / 3 = u by omega, show 3 * u + r = k by omega]
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

theorem lp_mul_cls {x y : BitVec 32} {r s : ℕ} (hr : r < 3) (hs : s < 3) (hx : Cls x r 16) (hy : Cls y s 16) :
    lp x * lp y = X ^ (r + s) * expand (ZMod 2) 3 ((cp x r * cp y s).map (Nat.castRingHom (ZMod 2))) := by
  rw [lp_cls hr hx, lp_cls hs hy, Polynomial.map_mul, map_mul, pow_add]
  ring

/-- The integer product's bits of the class `r + s` are the carry-less product's. -/
theorem lbit_mul_cls {x y : BitVec 32} {r s : ℕ} (hr : r < 3) (hs : s < 3) (hx : Cls x r 16)
    (hy : Cls y s 16) {k : ℕ} (hk : k % 3 = (r + s) % 3) :
    lbit ((x * y).getLsbD k) = (lp x * lp y).coeff k := by
  rw [lp_mul_cls hr hs hx hy, coeff_X_pow_mul']
  split_ifs with h
  · obtain ⟨d, rfl⟩ : ∃ d, k = 3 * d + (r + s) := ⟨(k - (r + s)) / 3, by omega_using [hk, h]⟩
    have hdv : 3 ∣ 3 * d + (r + s) - (r + s) := ⟨d, by omega_using []⟩
    rw [coeff_expand (by norm_num)]
    simp only [hdv, ↓reduceIte]
    rw [coeff_map, getLsbD_mul_cls hr hs hx hy,
      show (3 * d + (r + s) - (r + s)) / 3 = d by omega_using [], lbit_parity]
    rfl
  · rw [← BitVec.testBit_toNat, BitVec.toNat_mul, Nat.mod_eq_of_lt (mul_lt_cls hx hy), toNat_cls hr hx,
      toNat_cls hs hy,
      show 2 ^ r * (cp x r).eval 8 * (2 ^ s * (cp y s).eval 8) =
        2 ^ (r + s) * ((cp x r).eval 8 * (cp y s).eval 8) by rw [pow_add]; ring,
      Nat.testBit_two_pow_mul, decide_eq_false h, Bool.false_and]
    rfl

/-- The carry-less product has no bits outside the class `r + s`. -/
theorem coeff_mul_cls_ne {x y : BitVec 32} {r s : ℕ} (hr : r < 3) (hs : s < 3) (hx : Cls x r 16)
    (hy : Cls y s 16) {k : ℕ} (hk : k % 3 ≠ (r + s) % 3) : (lp x * lp y).coeff k = 0 := by
  rw [lp_mul_cls hr hs hx hy, coeff_X_pow_mul']
  split_ifs with h
  · have hdv : ¬ 3 ∣ k - (r + s) := by rintro ⟨d, hd⟩; omega_using [hk, h, hd]
    rw [coeff_expand (by norm_num)]
    simp only [hdv, ↓reduceIte]
  · rfl

/-! ## The masks -/

/-- The bits below 16 congruent to `i` modulo 3: the mask of a factor's class `i`. -/
def cM : ℕ → BitVec 32
  | 0 => 0x9249#32
  | 1 => 0x9249#32 >>> 2
  | _ => 0x9249#32 >>> 1

/-- The bits congruent to `i` modulo 3: the mask of a product's class `i`. -/
def oM : ℕ → BitVec 32
  | 0 => 0x49249249#32
  | 1 => 0x49249249#32 <<< 1
  | _ => 0x49249249#32 <<< 2

theorem getLsbD_cM {i : ℕ} (hi : i < 3) {j : ℕ} (hj : j < 32) :
    (cM i).getLsbD j = decide (j < 16 ∧ j % 3 = i) := by
  revert j
  interval_cases i <;> decide

theorem getLsbD_oM {i : ℕ} (hi : i < 3) {j : ℕ} (hj : j < 32) : (oM i).getLsbD j = decide (j % 3 = i) := by
  revert j
  interval_cases i <;> decide

theorem cls_cM (a : BitVec 32) {i : ℕ} (hi : i < 3) : Cls (a &&& cM i) i 16 := by
  intro j hj
  rw [BitVec.getLsbD_and, Bool.and_eq_true] at hj
  obtain ⟨h1, h2⟩ := hj
  have hj32 : j < 32 := by
    by_contra h
    rw [BitVec.getLsbD_of_ge a j (by omega_using [h])] at h1
    exact Bool.false_ne_true h1
  rw [getLsbD_cM hi hj32] at h2
  have := of_decide_eq_true h2
  exact ⟨this.2, this.1⟩

/-- The low half of a word, as a polynomial. -/
noncomputable abbrev lp16 (a : BitVec 32) : (ZMod 2)[X] := lp (a.setWidth 16)

theorem coeff_lp16 (a : BitVec 32) (n : ℕ) : (lp16 a).coeff n = lbit (decide (n < 16) && a.getLsbD n) := by
  rw [coeff_lp, BitVec.getLsbD_setWidth]

theorem lp16_split (a : BitVec 32) :
    lp16 a = lp (a &&& cM 0) + lp (a &&& cM 1) + lp (a &&& cM 2) := by
  ext n
  simp only [coeff_add, coeff_lp, BitVec.getLsbD_and, BitVec.getLsbD_setWidth]
  by_cases hn : n < 32
  · rw [getLsbD_cM (by norm_num) hn, getLsbD_cM (by norm_num) hn, getLsbD_cM (by norm_num) hn]
    have : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
    by_cases h16 : n < 16 <;> cases a.getLsbD n <;> interval_cases h : n % 3 <;> simp [lbit, h16]
  · simp [BitVec.getLsbD_of_ge a n (by omega_using [hn]), lbit]

theorem lp16_xor (a b : BitVec 32) : lp16 (a ^^^ b) = lp16 a + lp16 b := by
  ext n
  simp only [coeff_add, coeff_lp16, BitVec.getLsbD_xor]
  by_cases h16 : n < 16
  · simp only [h16, decide_true, Bool.true_and, lbit_xor]
  · simp [h16, lbit]

/-- The product of two 16-bit polynomials has no term of degree 31 or more. -/
theorem coeff_mul_lp16 (a b : BitVec 32) {k : ℕ} (hk : 31 ≤ k) : (lp16 a * lp16 b).coeff k = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  rcases Nat.lt_or_ge ij.1 16 with h | h
  · rw [coeff_lp16 b, decide_eq_false (by omega_using [hk, hij, h]), Bool.false_and]
    simp [lbit]
  · rw [coeff_lp16 a, decide_eq_false (by omega_using [h]), Bool.false_and]
    simp [lbit]

/-! ## A 32-bit carry-less product of 16-bit values -/

/-- The words `zₜ` of the code: the products of the parts of `a` and `b` whose
classes add up to `t`, `a`'s parts in order. -/
def zc (a b : BitVec 32) (t : ℕ) : BitVec 32 :=
  (a &&& cM 0) * (b &&& cM t) ^^^ (a &&& cM 1) * (b &&& cM ((t + 2) % 3)) ^^^
    (a &&& cM 2) * (b &&& cM ((t + 1) % 3))

/-- The class `t` of each `zₜ`, together: the carry-less product of the low
halves of `a` and `b`. -/
def h3 (a b : BitVec 32) : BitVec 32 :=
  (zc a b 0 &&& oM 0) ||| (zc a b 1 &&& oM 1) ||| (zc a b 2 &&& oM 2)

theorem lp_h3 (a b : BitVec 32) : lp (h3 a b) = lp16 a * lp16 b := by
  ext k
  rw [coeff_lp]
  by_cases hk : k < 32
  · rw [lp16_split a, lp16_split b]
    have c : ∀ i j, i < 3 → j < 3 → (i + j) % 3 = k % 3 →
        lbit (((a &&& cM i) * (b &&& cM j)).getLsbD k) = (lp (a &&& cM i) * lp (b &&& cM j)).coeff k :=
      fun i j hi hj h => lbit_mul_cls hi hj (cls_cM a hi) (cls_cM b hj) h.symm
    have z : ∀ i j, i < 3 → j < 3 → (i + j) % 3 ≠ k % 3 → (lp (a &&& cM i) * lp (b &&& cM j)).coeff k = 0 :=
      fun i j hi hj h => coeff_mul_cls_ne hi hj (cls_cM a hi) (cls_cM b hj) (Ne.symm h)
    simp (disch := omega_arith) only [h3, zc, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor,
      getLsbD_oM, add_mul, mul_add, coeff_add]
    have : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases h : k % 3 <;> simp only [Nat.reduceEqDiff, decide_true, decide_false, Bool.and_true,
      Bool.and_false, Bool.or_false, Bool.false_or, lbit_xor]
    · rw [c 0 0 (by norm_num) (by norm_num) (by omega_using [h]), c 1 2 (by norm_num) (by norm_num) (by omega_using [h]),
        c 2 1 (by norm_num) (by norm_num) (by omega_using [h])]
      linear_combination -(z 0 1 (by norm_num) (by norm_num) (by omega_using [h])
        + z 0 2 (by norm_num) (by norm_num) (by omega_using [h])
        + z 1 0 (by norm_num) (by norm_num) (by omega_using [h])
        + z 1 1 (by norm_num) (by norm_num) (by omega_using [h])
        + z 2 0 (by norm_num) (by norm_num) (by omega_using [h])
        + z 2 2 (by norm_num) (by norm_num) (by omega_using [h]))
    · rw [c 0 1 (by norm_num) (by norm_num) (by omega_using [h]), c 1 0 (by norm_num) (by norm_num) (by omega_using [h]),
        c 2 2 (by norm_num) (by norm_num) (by omega_using [h])]
      linear_combination -(z 0 0 (by norm_num) (by norm_num) (by omega_using [h])
        + z 0 2 (by norm_num) (by norm_num) (by omega_using [h])
        + z 1 1 (by norm_num) (by norm_num) (by omega_using [h])
        + z 1 2 (by norm_num) (by norm_num) (by omega_using [h])
        + z 2 0 (by norm_num) (by norm_num) (by omega_using [h])
        + z 2 1 (by norm_num) (by norm_num) (by omega_using [h]))
    · rw [c 0 2 (by norm_num) (by norm_num) (by omega_using [h]), c 1 1 (by norm_num) (by norm_num) (by omega_using [h]),
        c 2 0 (by norm_num) (by norm_num) (by omega_using [h])]
      linear_combination -(z 0 0 (by norm_num) (by norm_num) (by omega_using [h])
        + z 0 1 (by norm_num) (by norm_num) (by omega_using [h])
        + z 1 0 (by norm_num) (by norm_num) (by omega_using [h])
        + z 1 2 (by norm_num) (by norm_num) (by omega_using [h])
        + z 2 1 (by norm_num) (by norm_num) (by omega_using [h])
        + z 2 2 (by norm_num) (by norm_num) (by omega_using [h]))
  · rw [BitVec.getLsbD_of_ge _ k (by omega_using [hk]), coeff_mul_lp16 a b (by omega_using [hk])]
    rfl

/-! ## 32 × 32 bits by Karatsuba -/

theorem lp_lo_hi16 (w : BitVec 32) : lp w = lp16 w + X ^ 16 * lp16 (w >>> 16) := by
  ext k
  rw [coeff_add, coeff_X_pow_mul', coeff_lp, coeff_lp16]
  split_ifs with h
  · rw [coeff_lp16, BitVec.getLsbD_ushiftRight, show 16 + (k - 16) = k by omega_using [h]]
    by_cases hk : k < 32
    · simp [show ¬ k < 16 by omega_using [h], show k - 16 < 16 by omega_using [hk], lbit]
    · simp [BitVec.getLsbD_of_ge w k (by omega_using [hk]), lbit]
  · simp [show k < 16 by omega_using [h]]

theorem lp_shl16 (m : BitVec 32) : lp (m <<< 16) = X ^ 16 * lp16 m := by
  ext k
  rw [coeff_X_pow_mul', coeff_lp, BitVec.getLsbD_shiftLeft]
  split_ifs with h
  · rw [coeff_lp16]
    by_cases hk : k < 32
    · simp [hk, show ¬ k < 16 by omega_using [h], show k - 16 < 16 by omega_using [hk]]
    · simp [hk, show ¬ k - 16 < 16 by omega_using [hk], lbit]
  · simp [show k < 16 by omega_using [h], lbit]

theorem lp_shr16 (m : BitVec 32) : lp (m >>> 16) = lp16 (m >>> 16) := by
  ext k
  rw [coeff_lp, coeff_lp16]
  by_cases hk : k < 16
  · simp [hk]
  · rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_of_ge m (16 + k) (by omega_using [hk])]; simp

/-- Karatsuba's middle term of a 32-bit product: the product of the sums of
the halves, less the products of the low halves and of the high halves. -/
def mid32 (w k : BitVec 32) : BitVec 32 :=
  h3 (w ^^^ w >>> 16) (k ^^^ k >>> 16) ^^^ h3 w k ^^^ h3 (w >>> 16) (k >>> 16)

/-- The 64-bit carry-less product of two words, by three products of
halves: its low and high words. -/
def m32 (w k : BitVec 32) : BitVec 32 × BitVec 32 :=
  (h3 w k ^^^ mid32 w k <<< 16, h3 (w >>> 16) (k >>> 16) ^^^ mid32 w k >>> 16)

theorem lp_m32 (w k : BitVec 32) : lp (m32 w k).1 + X ^ 32 * lp (m32 w k).2 = lp w * lp k := by
  have eL := lp_h3 w k
  have eH := lp_h3 (w >>> 16) (k >>> 16)
  have eM := lp_h3 (w ^^^ w >>> 16) (k ^^^ k >>> 16)
  rw [lp16_xor, lp16_xor] at eM
  have hm := lp_lo_hi16 (mid32 w k)
  have hmid : lp (mid32 w k) =
      lp (h3 (w ^^^ w >>> 16) (k ^^^ k >>> 16)) + lp (h3 w k) + lp (h3 (w >>> 16) (k >>> 16)) := by
    rw [mid32, lp_xor, lp_xor]
  show lp (h3 w k ^^^ mid32 w k <<< 16) + X ^ 32 * lp (h3 (w >>> 16) (k >>> 16) ^^^ mid32 w k >>> 16) = _
  rw [lp_xor, lp_xor, lp_shl16, lp_shr16, lp_lo_hi16 w, lp_lo_hi16 k]
  linear_combination (-X ^ 16 : (ZMod 2)[X]) * hm + X ^ 16 * hmid + X ^ 16 * eM + (1 + X ^ 16) * eL +
    (X ^ 32 + X ^ 16) * eH + X ^ 16 * (lp16 w * lp16 k + lp16 (w >>> 16) * lp16 (k >>> 16)) * two_P

/-! ## 64 × 64 and 128 × 128 bits by Karatsuba -/

/-- Four words, the least significant first for a product, the first of a
block first for a block (`blk`). -/
abbrev W4 : Type := BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32

/-- The polynomial of four words, the least significant first. -/
noncomputable def v4 (r : W4) : (ZMod 2)[X] :=
  lp r.1 + X ^ 32 * lp r.2.1 + X ^ 64 * lp r.2.2.1 + X ^ 96 * lp r.2.2.2

/-- The 128-bit carry-less product of two 64-bit values, given as their low
words, their high words and the sums of the two. -/
def m64 (xl xh xm kl kh km : BitVec 32) : W4 :=
  ((m32 xl kl).1,
   (m32 xl kl).2 ^^^ ((m32 xm km).1 ^^^ (m32 xl kl).1 ^^^ (m32 xh kh).1),
   (m32 xh kh).1 ^^^ ((m32 xm km).2 ^^^ (m32 xl kl).2 ^^^ (m32 xh kh).2),
   (m32 xh kh).2)

theorem lp_m64 (xl xh kl kh : BitVec 32) :
    v4 (m64 xl xh (xl ^^^ xh) kl kh (kl ^^^ kh)) = (lp xl + X ^ 32 * lp xh) * (lp kl + X ^ 32 * lp kh) := by
  have eL := lp_m32 xl kl
  have eH := lp_m32 xh kh
  have eM := lp_m32 (xl ^^^ xh) (kl ^^^ kh)
  rw [lp_xor, lp_xor] at eM
  simp only [v4, m64, lp_xor]
  linear_combination (1 + X ^ 32) * eL + X ^ 32 * eM + (X ^ 32 + X ^ 64) * eH +
    X ^ 32 * (lp xl * lp kl + lp xh * lp kh) * two_P

/-- The 256 bits of a product from Karatsuba's three: its low four words and
its high four. -/
def kar (l h m : W4) : W4 × W4 :=
  ((l.1, l.2.1, l.2.2.1 ^^^ (m.1 ^^^ l.1 ^^^ h.1), l.2.2.2 ^^^ (m.2.1 ^^^ l.2.1 ^^^ h.2.1)),
   (h.1 ^^^ (m.2.2.1 ^^^ l.2.2.1 ^^^ h.2.2.1), h.2.1 ^^^ (m.2.2.2 ^^^ l.2.2.2 ^^^ h.2.2.2), h.2.2.1,
    h.2.2.2))

theorem v_kar (l h m : W4) :
    v4 (kar l h m).1 + X ^ 128 * v4 (kar l h m).2 = v4 l + X ^ 64 * (v4 m + v4 l + v4 h) + X ^ 128 * v4 h := by
  simp only [kar, v4, lp_xor]; ring

/-- A block of four words, the first bytes first. -/
def blk (r : W4) : BitVec 128 := r.1 ++ r.2.1 ++ r.2.2.1 ++ r.2.2.2

theorem lp_blk (r : W4) :
    lp (blk r) = lp r.2.2.2 + X ^ 32 * lp r.2.2.1 + X ^ 64 * lp r.2.1 + X ^ 96 * lp r.1 := by
  simp only [blk, lp_append]; ring

/-- The 256-bit carry-less product of two blocks. -/
def prod (w k : W4) : W4 × W4 :=
  kar (m64 w.2.2.2 w.2.2.1 (w.2.2.2 ^^^ w.2.2.1) k.2.2.2 k.2.2.1 (k.2.2.2 ^^^ k.2.2.1))
    (m64 w.2.1 w.1 (w.2.1 ^^^ w.1) k.2.1 k.1 (k.2.1 ^^^ k.1))
    (m64 (w.2.2.2 ^^^ w.2.1) (w.2.2.1 ^^^ w.1) (w.2.2.2 ^^^ w.2.1 ^^^ (w.2.2.1 ^^^ w.1))
      (k.2.2.2 ^^^ k.2.1) (k.2.2.1 ^^^ k.1) (k.2.2.2 ^^^ k.2.1 ^^^ (k.2.2.1 ^^^ k.1)))

theorem v_prod (w k : W4) : v4 (prod w k).1 + X ^ 128 * v4 (prod w k).2 = lp (blk w) * lp (blk k) := by
  have eL := lp_m64 w.2.2.2 w.2.2.1 k.2.2.2 k.2.2.1
  have eH := lp_m64 w.2.1 w.1 k.2.1 k.1
  have eM := lp_m64 (w.2.2.2 ^^^ w.2.1) (w.2.2.1 ^^^ w.1) (k.2.2.2 ^^^ k.2.1) (k.2.2.1 ^^^ k.1)
  simp only [lp_xor] at eM
  rw [prod, v_kar, lp_blk, lp_blk]
  linear_combination (1 + X ^ 64) * eL + X ^ 64 * eM + (X ^ 64 + X ^ 128) * eH +
    X ^ 64 * ((lp w.2.2.2 + X ^ 32 * lp w.2.2.1) * (lp k.2.2.2 + X ^ 32 * lp k.2.2.1) +
      (lp w.2.1 + X ^ 32 * lp w.1) * (lp k.2.1 + X ^ 32 * lp k.1)) * two_P

/-! ## From integers' bit order to blocks' -/

section Ghash
open VG.Proof.Gcm.Poly

theorem natDegree_lp {n : ℕ} (v : BitVec n) : (lp v).natDegree ≤ n - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_lp, BitVec.getLsbD_of_ge v N (by omega_using [hN])]; rfl

/-- A value's polynomial with the most significant bit first is the other's reflection. -/
theorem gp_eq_reflect {n : ℕ} (v : BitVec n) (hn : 0 < n) : gp v = reflect (n - 1) (lp v) := by
  ext k
  rw [coeff_gp, coeff_reflect, coeff_lp]
  by_cases hk : k < n
  · rw [revAt_le (by omega_using [hk]), BitVec.getMsbD_eq_getLsbD, decide_eq_true hk, Bool.true_and]; rfl
  · rw [revAt_eq_self_of_lt (by omega_using [hk, hn]), BitVec.getLsbD_of_ge v k (by omega_using [hk]),
      show v.getMsbD k = false by simp [BitVec.getMsbD, hk]]; rfl

/-- A 256-bit carry-less product of two blocks is the product of their
polynomials times `X`. -/
theorem gp_of_lp {a b : BitVec 128} {c : BitVec 256} (h : lp c = lp a * lp b) : gp c = X * gp a * gp b := by
  have ha : (lp a).natDegree ≤ 127 := natDegree_lp a
  have hb : (lp b).natDegree ≤ 127 := natDegree_lp b
  have hab : (lp a * lp b).natDegree ≤ 254 := natDegree_mul_le.trans (by omega_using [ha, hb])
  have e3 : reflect 1 (1 : (ZMod 2)[X]) = X := by simp
  rw [gp_eq_reflect c (by decide), h, gp_eq_reflect a (by decide), gp_eq_reflect b (by decide)]
  calc reflect 255 (lp a * lp b) = reflect (254 + 1) (lp a * lp b * 1) := by rw [mul_one]
    _ = reflect (127 + 127) (lp a * lp b) * reflect 1 1 := reflect_mul _ _ hab (by simp)
    _ = X * reflect 127 (lp a) * reflect 127 (lp b) := by rw [reflect_mul _ _ ha hb, e3]; ring

/-- The class of a word's polynomial. -/
noncomputable def ψ (q : BitVec 32) : Q := AdjoinRoot.mk g (gp q)

theorem ψ_xor (a b : BitVec 32) : ψ (a ^^^ b) = ψ a + ψ b := by
  simp only [ψ, gp_xor, map_add]

theorem φ_blk (r : W4) : φ (blk r) = ψ r.1 + x ^ 32 * ψ r.2.1 + x ^ 64 * ψ r.2.2.1 + x ^ 96 * ψ r.2.2.2 := by
  simp only [φ, ψ, blk, gp_append, map_add, map_mul, map_pow, AdjoinRoot.mk_X]

/-- The eight words of a product as 256 bits. -/
def cat8 (f : W4 × W4) : BitVec 256 :=
  f.2.2.2.2 ++ f.2.2.2.1 ++ f.2.2.1 ++ f.2.1 ++ f.1.2.2.2 ++ f.1.2.2.1 ++ f.1.2.1 ++ f.1.1

theorem lp_cat8 (f : W4 × W4) : lp (cat8 f) = v4 f.1 + X ^ 128 * v4 f.2 := by
  simp only [cat8, lp_append, v4]; ring

theorem gp_cat8 (f : W4 × W4) :
    gp (cat8 f) = gp f.2.2.2.2 + X ^ 32 * gp f.2.2.2.1 + X ^ 64 * gp f.2.2.1 + X ^ 96 * gp f.2.1 +
      X ^ 128 * gp f.1.2.2.2 + X ^ 160 * gp f.1.2.2.1 + X ^ 192 * gp f.1.2.1 + X ^ 224 * gp f.1.1 := by
  simp only [cat8, gp_append]

/-- The product's words, the most significant the terms of the lowest degrees. -/
theorem ψ_prod (w k : W4) :
    ψ (prod w k).2.2.2.2 + x ^ 32 * ψ (prod w k).2.2.2.1 + x ^ 64 * ψ (prod w k).2.2.1 +
      x ^ 96 * ψ (prod w k).2.1 + x ^ 128 * ψ (prod w k).1.2.2.2 + x ^ 160 * ψ (prod w k).1.2.2.1 +
      x ^ 192 * ψ (prod w k).1.2.1 + x ^ 224 * ψ (prod w k).1.1 = x * φ (blk w) * φ (blk k) := by
  have h := congrArg (AdjoinRoot.mk g) (gp_of_lp (c := cat8 (prod w k)) (a := blk w) (b := blk k)
    (by rw [lp_cat8, v_prod]))
  rw [gp_cat8] at h
  simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_X] at h
  exact h

/-! ## The reduction -/

theorem gp_shr_shl (w : BitVec 32) {s : ℕ} (hs : 0 < s) (hs' : s < 32) :
    gp (w >>> s) + X ^ 32 * gp (w <<< (32 - s)) = X ^ s * gp w := by
  ext d
  rw [coeff_add, coeff_gp, coeff_X_pow_mul', coeff_X_pow_mul', coeff_gp, coeff_gp,
    BitVec.getMsbD_ushiftRight, BitVec.getMsbD_shiftLeft]
  by_cases h1 : s ≤ d
  · by_cases h2 : 32 ≤ d
    · simp only [h1, h2, ↓reduceIte, decide_eq_false (show ¬ d < 32 by omega), Bool.false_and,
        show d - 32 + (32 - s) = d - s by omega]
      simp only [bit, Bool.false_eq_true, ↓reduceIte, zero_add]
    · simp only [h1, h2, ↓reduceIte, decide_eq_true (show d < 32 by omega),
        decide_eq_false (show ¬ d < s by omega), Bool.not_false, Bool.true_and, add_zero]
  · simp only [h1, show ¬ 32 ≤ d by omega, ↓reduceIte,
      decide_eq_true (show d < s by omega), Bool.not_true, Bool.false_and, Bool.and_false, add_zero]
    rfl

theorem ψ_shr_shl (w : BitVec 32) {s : ℕ} (hs : 0 < s) (hs' : s < 32) :
    ψ (w >>> s) + x ^ 32 * ψ (w <<< (32 - s)) = x ^ s * ψ w := by
  have := congrArg (AdjoinRoot.mk g) (gp_shr_shl w hs hs')
  simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_X] at this
  exact this

/-- What a fold adds to the word of the lower degrees, -/
def foldLo (lo w : BitVec 32) : BitVec 32 := lo ^^^ w ^^^ w >>> 1 ^^^ w >>> 2 ^^^ w >>> 7

/-- and to the next. -/
def foldHi (hi w : BitVec 32) : BitVec 32 := hi ^^^ w <<< 31 ^^^ w <<< 30 ^^^ w <<< 25

/-- A word `w` of degrees 128 and more, folded into the two words 128 below. -/
theorem ψ_fold (lo hi w : BitVec 32) :
    ψ (foldLo lo w) + x ^ 32 * ψ (foldHi hi w) = ψ lo + x ^ 32 * ψ hi + x ^ 128 * ψ w := by
  have e1 := ψ_shr_shl w (s := 1) (by decide) (by decide)
  have e2 := ψ_shr_shl w (s := 2) (by decide) (by decide)
  have e7 := ψ_shr_shl w (s := 7) (by decide) (by decide)
  simp only [foldLo, foldHi, ψ_xor]
  simp only [Nat.reduceSub] at e1 e2 e7
  linear_combination e1 + e2 + e7 - ψ w * x128

/-- The reduction of a product's eight words `f₀ … f₇` (the least significant
first, which holds the highest degrees): `f₀`, `f₁`, `f₂` and then `f₃` are
folded into the words 128 degrees below. -/
def red (f0 f1 f2 f3 f4 f5 f6 f7 : BitVec 32) : W4 :=
  (foldLo f7 (foldHi f3 f0), foldHi (foldLo f6 f2) (foldHi f3 f0), foldHi (foldLo f5 f1) f2,
    foldHi (foldLo f4 f0) f1)

theorem φ_red (f0 f1 f2 f3 f4 f5 f6 f7 : BitVec 32) :
    φ (blk (red f0 f1 f2 f3 f4 f5 f6 f7)) =
      ψ f7 + x ^ 32 * ψ f6 + x ^ 64 * ψ f5 + x ^ 96 * ψ f4 + x ^ 128 * ψ f3 + x ^ 160 * ψ f2 +
        x ^ 192 * ψ f1 + x ^ 224 * ψ f0 := by
  have e1 := ψ_fold f4 f3 f0
  have e2 := ψ_fold f5 (foldLo f4 f0) f1
  have e3 := ψ_fold f6 (foldLo f5 f1) f2
  have e4 := ψ_fold f7 (foldLo f6 f2) (foldHi f3 f0)
  rw [φ_blk]
  simp only [red]
  linear_combination e4 + x ^ 32 * e3 + x ^ 64 * e2 + x ^ 96 * e1

/-! ## The key -/

/-- Whether a word's first bit is set, in `Q`. -/
noncomputable def mb (q : BitVec 32) : Q := if q.getMsbD 0 then 1 else 0

theorem gp_shl1 (q : BitVec 32) :
    gp q = (if q.getMsbD 0 then (1 : P) else 0) + X * gp (q <<< 1) := by
  ext d
  rw [coeff_add, coeff_gp]
  rcases d with _ | d
  · rw [coeff_X_mul_zero, add_zero]
    cases q.getMsbD 0 <;> simp [bit]
  · rw [coeff_X_mul, coeff_gp, BitVec.getMsbD_shiftLeft]
    have h0 : ((if q.getMsbD 0 then (1 : P) else 0)).coeff (d + 1) = 0 := by
      split_ifs
      · rw [coeff_one]; simp
      · rw [coeff_zero]
    rw [h0, zero_add]

theorem gp_ushr31 (q : BitVec 32) : gp (q >>> 31) = if q.getMsbD 0 then (X : P) ^ 31 else 0 := by
  ext d
  rw [coeff_gp, BitVec.getMsbD_ushiftRight]
  by_cases hd : d = 31
  · subst hd; cases h : q.getMsbD 0 <;> simp [bit]
  · have : (decide (d < 32) && (!decide (d < 31) && q.getMsbD (d - 31))) = false := by
      by_cases h : d < 31
      · simp [h]
      · simp [show ¬ d < 32 by omega_using [hd, h]]
    rw [this]; split_ifs <;> simp [bit, coeff_X_pow, hd]

theorem ψ_shl1 (q : BitVec 32) : ψ q = mb q + x * ψ (q <<< 1) := by
  conv_lhs => rw [ψ, gp_shl1]
  simp only [ψ, mb, map_add, map_mul, AdjoinRoot.mk_X]; split_ifs <;> simp

theorem ψ_ushr31 (q : BitVec 32) : ψ (q >>> 31) = mb q * x ^ 31 := by
  simp only [ψ, mb, gp_ushr31]; split_ifs <;> simp [AdjoinRoot.mk_X]

theorem gp_one32 : gp (1#32) = (X : P) ^ 31 := by
  have h := gp_ushr31 (BitVec.allOnes 32)
  rw [show BitVec.allOnes 32 >>> 31 = 1#32 by decide, show (BitVec.allOnes 32).getMsbD 0 = true by decide] at h
  simpa using h

theorem ushr31 (q : BitVec 32) : q >>> 31 = if q.getMsbD 0 then 1#32 else 0#32 :=
  gp_ext (by rw [gp_ushr31]; split_ifs <;> simp [gp_one32, gp_zero'])

/-- The terms `1 + x + x⁶` of `x⁻¹`. -/
theorem ψ_c2 : ψ 0xC2000000#32 = 1 + x + x ^ 6 := by
  have hb : ∀ d < 32, (0xC2000000#32).getMsbD d = (d = 0 || d = 1 || d = 6) := by decide
  have h : gp 0xC2000000#32 = 1 + X + X ^ 6 := by
    ext d
    rw [coeff_gp]
    simp only [coeff_add, coeff_X_pow, coeff_X, coeff_one]
    by_cases hd : d < 32
    · rw [hb d hd]
      rcases (by omega_using [] : d = 0 ∨ d = 1 ∨ d = 6 ∨ (d ≠ 0 ∧ d ≠ 1 ∧ d ≠ 6)) with
        rfl | rfl | rfl | ⟨h0, h1, h6⟩
      · decide
      · decide
      · decide
      · simp only [bit, h0, decide_false, h1, Bool.or_self, h6, Bool.false_eq_true, ↓reduceIte,
          show (1 : Nat) ≠ d from fun h => h1 h.symm, add_zero]
    · have e : (0xC2000000#32).getMsbD d = false := by
        simp only [BitVec.getMsbD, Nat.add_one_sub_one, Bool.and_eq_false_imp, decide_eq_true_eq]
        omega_using [hd]
      rw [e]
      simp only [bit, Bool.false_eq_true, ↓reduceIte, show d ≠ 0 by omega_using [hd],
        show (1 : Nat) ≠ d by omega_using [hd], add_zero, show d ≠ 6 by omega_using [hd]]
  simp only [ψ, h, map_add, map_one, AdjoinRoot.mk_X, map_pow]

theorem ψ_mask (q : BitVec 32) : ψ ((0#32 - q >>> 31) &&& 0xC2000000#32) = mb q * (1 + x + x ^ 6) := by
  rw [ushr31, mb]
  split_ifs
  · rw [show 0#32 - 1#32 = BitVec.allOnes 32 by decide, BitVec.allOnes_and, ψ_c2, one_mul]
  · simp [ψ, gp_zero']

/-- The key `H · x⁻¹`: the block shifted up by one bit, around, and `1 + x + x⁶`
of `x⁻¹ = 1 + x + x⁶ + x¹²⁷` added if its constant term was set. -/
def keyW (h : W4) : W4 :=
  (h.1 <<< 1 ^^^ h.2.1 >>> 31 ^^^ ((0#32 - h.1 >>> 31) &&& 0xC2000000#32),
   h.2.1 <<< 1 ^^^ h.2.2.1 >>> 31, h.2.2.1 <<< 1 ^^^ h.2.2.2 >>> 31, h.2.2.2 <<< 1 ^^^ h.1 >>> 31)

theorem x_φ_keyW (h : W4) : x * φ (blk (keyW h)) = φ (blk h) := by
  rw [φ_blk, φ_blk, ψ_shl1 h.1, ψ_shl1 h.2.1, ψ_shl1 h.2.2.1, ψ_shl1 h.2.2.2]
  simp only [keyW, ψ_xor, ψ_ushr31, ψ_mask]
  linear_combination mb h.1 * x128 + mb h.1 * (x + x ^ 2 + x ^ 7) * two_Q

/-! ## A block -/

/-- One block's product by the key `k` (`keyW`), as the code computes it. -/
def mulW (w k : W4) : W4 :=
  red (prod w k).1.1 (prod w k).1.2.1 (prod w k).1.2.2.1 (prod w k).1.2.2.2 (prod w k).2.1
    (prod w k).2.2.1 (prod w k).2.2.2.1 (prod w k).2.2.2.2

/-- The block product of SP 800-38D. -/
theorem mulW_eq (y h : W4) : blk (mulW y (keyW h)) = Spec.Gcm.mul (blk y) (blk h) := by
  apply φ_inj
  rw [φ_mul, mulW, φ_red, ψ_prod, ← x_φ_keyW h]
  ring

end Ghash

end VG.Proof.Gcm.Holes16
