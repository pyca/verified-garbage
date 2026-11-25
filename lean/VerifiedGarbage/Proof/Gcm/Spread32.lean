module

public import VerifiedGarbage.Proof.Gcm.Spread
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Carry-less products from 32-bit integer products of 16-bit words

Untrusted: everything here is checked by Lean. Three classes modulo 3 of
16-bit words (`cm16`), then Karatsuba's method, and the key and the reduction
in 32-bit words.
-/

@[expose] public section

namespace VG.Proof.Gcm.Spread

open Polynomial VG.VectorCrypto VG.Proof.Gcm.Poly VG.Proof.Gcm.Clmul

/-! ## Words as polynomials -/

theorem lp_append {n m : Nat} (a : BitVec n) (b : BitVec m) : lp (a ++ b) = lp b + X ^ m * lp a := by
  ext d
  rw [coeff_add, coeff_X_pow_mul', coeff_lp, coeff_lp, coeff_lp, BitVec.getLsbD_append]
  by_cases h : d < m
  · simp only [h, ite_true, show ¬ m ≤ d by omega, ite_false, add_zero]
  · simp only [h, ite_false, show m ≤ d by omega, ite_true, BitVec.getLsbD_of_ge b d (by omega)]
    simp [bit]

/-- A word shifted across two words. -/
theorem lp_shift (v : BitVec 32) {k : Nat} (hk : k ≤ 32) : lp (v <<< k) + X ^ 32 * lp (v >>> (32 - k)) = X ^ k * lp v := by
  ext d
  rw [coeff_add, coeff_X_pow_mul', coeff_X_pow_mul', coeff_lp, coeff_lp, coeff_lp, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight]
  by_cases h1 : d < 32
  · by_cases h2 : d < k
    · simp [h1, h2, show ¬ 32 ≤ d by omega, show ¬ k ≤ d by omega, bit]
    · simp [h1, h2, show ¬ 32 ≤ d by omega, show k ≤ d by omega]
  · by_cases h2 : d < k
    · omega
    · simp [h1, show 32 ≤ d by omega, show k ≤ d by omega, show 32 - k + (d - 32) = d - k by omega, bit]

/-! ## 16-bit words -/

/-- The positions congruent to `r` modulo 3. -/
def c3 (r : Nat) : BitVec 32 :=
  match r with | 0 => 0x49249249#32 | 1 => 0x92492492#32 | _ => 0x24924924#32

def meet3 (a b : BitVec 32) (r : Nat) : BitVec 32 :=
  (a &&& c3 0) * (b &&& c3 (r % 3)) ^^^ (a &&& c3 1) * (b &&& c3 ((r + 2) % 3)) ^^^ (a &&& c3 2) * (b &&& c3 ((r + 1) % 3))

/-- The carry-less product of two 16-bit words, from nine integer products. -/
def cm16 (a b : BitVec 32) : BitVec 32 := (meet3 a b 0 &&& c3 0) ^^^ (meet3 a b 1 &&& c3 1) ^^^ (meet3 a b 2 &&& c3 2)

def Low16 (a : BitVec 32) : Prop := ∀ p, a.getLsbD p = true → p < 16

theorem c3_class : ∀ i < 3, ∀ p < 32, (c3 i).getLsbD p = decide (p % 3 = i) := by decide +kernel

theorem inClass_c3 (a : BitVec 32) {i : Nat} (hi : i < 3) : InClass 3 i ((a &&& c3 i).setWidth 64) := by
  intro p hp
  rw [BitVec.getLsbD_setWidth, Bool.and_eq_true] at hp
  have hp := hp.2
  have h32 : p < 32 := BitVec.lt_of_getLsbD hp
  rw [BitVec.getLsbD_and, c3_class i hi p h32, Bool.and_eq_true, decide_eq_true_eq] at hp
  exact hp.2

theorem getLsbD_mul32 (a b : BitVec 32) {p : Nat} (hp : p < 32) :
    (a * b).getLsbD p = ((a.setWidth 64).setWidth 128 * (b.setWidth 64).setWidth 128).getLsbD p := by
  have h : a * b = ((a.setWidth 64).setWidth 128 * (b.setWidth 64).setWidth 128).setWidth 32 := by
    apply BitVec.eq_of_toNat_eq
    have ha := a.isLt
    have hb := b.isLt
    simp only [BitVec.toNat_mul, BitVec.toNat_setWidth]
    rw [Nat.mod_eq_of_lt (show a.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b.toNat < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show a.toNat < 2 ^ 128 by omega), Nat.mod_eq_of_lt (show b.toNat < 2 ^ 128 by omega),
      Nat.mod_mod_of_dvd _ (by decide)]
  rw [h, BitVec.getLsbD_setWidth, decide_eq_true hp, Bool.true_and]

theorem cp3_mask {a : BitVec 32} (ha : Low16 a) (b : BitVec 32) {i j r : Nat} (hi : i < 3) (hj : j < 3) (hr : r < 3)
    (h : (i + j) % 3 = r) {p : Nat} (hp : p < 32) :
    ((a &&& c3 i) * (b &&& c3 j) &&& c3 r).getLsbD p =
      (polyMul ((a &&& c3 i).setWidth 64) ((b &&& c3 j).setWidth 64)).getLsbD p := by
  rw [BitVec.getLsbD_and, c3_class r hr p hp, getLsbD_mul32 _ _ hp]
  by_cases hc : p % 3 = r
  · rw [decide_eq_true hc, Bool.and_true]
    refine getLsbD_mul (n := 15) (by decide) (inClass_c3 a hi) (inClass_c3 b hj) (fun q hq => ?_) (by decide) (by omega)
      (hc.trans h.symm)
    rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, Bool.and_eq_true, Bool.and_eq_true] at hq
    exact Nat.le_of_lt_succ (ha q hq.2.1)
  · rw [decide_eq_false hc, Bool.and_false]
    exact (getLsbD_polyMul_class (inClass_c3 a hi) (inClass_c3 b hj) (fun e => hc (e.trans h))).symm

theorem lp_setWidth (a : BitVec 32) : lp (a.setWidth 64) = lp a := by
  ext d
  rw [coeff_lp, coeff_lp, BitVec.getLsbD_setWidth]
  by_cases h : d < 64
  · rw [decide_eq_true h, Bool.true_and]
  · rw [decide_eq_false h, Bool.false_and, BitVec.getLsbD_of_ge a d (by omega)]

theorem split3 (a : BitVec 32) : (a &&& c3 0) ^^^ (a &&& c3 1) ^^^ (a &&& c3 2) = a := by
  rw [← and_xor, ← and_xor, show c3 0 ^^^ c3 1 ^^^ c3 2 = BitVec.allOnes 32 by decide, BitVec.and_allOnes]

theorem lp_cm16 {a b : BitVec 32} (ha : Low16 a) (hb : Low16 b) : lp (cm16 a b) = lp a * lp b := by
  have hm : ∀ r < 3, ∀ p < 32, (meet3 a b r &&& c3 r).getLsbD p =
      (polyMul ((a &&& c3 0).setWidth 64) ((b &&& c3 (r % 3)).setWidth 64) ^^^
        polyMul ((a &&& c3 1).setWidth 64) ((b &&& c3 ((r + 2) % 3)).setWidth 64) ^^^
        polyMul ((a &&& c3 2).setWidth 64) ((b &&& c3 ((r + 1) % 3)).setWidth 64)).getLsbD p := by
    intro r hr p hp
    rw [meet3, xor_and, xor_and]
    simp only [BitVec.getLsbD_xor]
    rw [cp3_mask ha b (by decide) (Nat.mod_lt _ (by decide)) hr (by omega) hp,
      cp3_mask ha b (by decide) (Nat.mod_lt _ (by decide)) hr (by omega) hp,
      cp3_mask ha b (by decide) (Nat.mod_lt _ (by decide)) hr (by omega) hp]
  have hdeg : ∀ d, ¬ d < 32 → (lp a * lp b).coeff d = 0 := by
    intro d hd
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun ⟨p, q⟩ hpq => ?_
    rw [Finset.mem_antidiagonal] at hpq
    simp only [coeff_lp]
    by_cases h1 : a.getLsbD p = true
    · have h1' := ha p h1
      have h2 : b.getLsbD q = false := by
        rw [← Bool.not_eq_true]; intro h2; have := hb q h2; omega
      rw [h2]; simp [bit]
    · rw [Bool.not_eq_true] at h1; rw [h1]; simp [bit]
  ext d
  by_cases hd : d < 32
  · rw [coeff_lp, cm16, BitVec.getLsbD_xor, BitVec.getLsbD_xor, hm 0 (by decide) d hd, hm 1 (by decide) d hd,
      hm 2 (by decide) d hd, ← BitVec.getLsbD_xor, ← BitVec.getLsbD_xor, ← coeff_lp]
    refine congrArg (fun q : P => q.coeff d) ?_
    conv_rhs => rw [← split3 a, ← split3 b]
    simp only [lp_xor, lp_polyMul, lp_setWidth, Nat.reduceMod, Nat.reduceAdd]
    ring
  · rw [hdeg d hd, coeff_lp, BitVec.getLsbD_of_ge _ d (by omega)]; simp [bit]

/-! ## 32-bit words -/

def lo16 (w : BitVec 32) : BitVec 32 := (w <<< 16) >>> 16
def hi16 (w : BitVec 32) : BitVec 32 := w >>> 16

theorem getLsbD_lo16 (w : BitVec 32) (p : Nat) : (lo16 w).getLsbD p = (decide (p < 16) && w.getLsbD p) := by
  rw [lo16, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  by_cases h : p < 16
  · simp only [h, decide_true, Bool.true_and, show 16 + p < 32 by omega, show ¬ 16 + p < 16 by omega, decide_false,
      Bool.not_false, Nat.add_sub_cancel_left]
  · simp only [h, decide_false, Bool.false_and, show ¬ 16 + p < 32 by omega]

theorem low_lo16 (w : BitVec 32) : Low16 (lo16 w) := fun p hp => by
  rw [getLsbD_lo16, Bool.and_eq_true, decide_eq_true_eq] at hp; exact hp.1

theorem low_hi16 (w : BitVec 32) : Low16 (hi16 w) := fun p hp => by
  rw [hi16, BitVec.getLsbD_ushiftRight] at hp
  have := BitVec.lt_of_getLsbD hp
  omega

theorem low16_xor {a b : BitVec 32} (ha : Low16 a) (hb : Low16 b) : Low16 (a ^^^ b) := fun p hp => by
  rw [BitVec.getLsbD_xor] at hp
  by_cases h : a.getLsbD p = true
  · exact ha p h
  · refine hb p ?_
    rw [Bool.not_eq_true] at h
    rwa [h, Bool.false_xor] at hp

theorem lp_lo_hi16 (w : BitVec 32) : lp w = lp (lo16 w) + X ^ 16 * lp (hi16 w) := by
  ext d
  rw [coeff_add, coeff_X_pow_mul', coeff_lp, coeff_lp, getLsbD_lo16]
  by_cases h : d < 16
  · simp only [h, decide_true, Bool.true_and, show ¬ 16 ≤ d by omega, ite_false, add_zero]
  · simp only [h, decide_false, Bool.false_and, show 16 ≤ d by omega, ite_true, coeff_lp, hi16,
      BitVec.getLsbD_ushiftRight, show 16 + (d - 16) = d by omega]
    simp [bit]

/-- The sum of a word's halves, in its high half. -/
theorem sum16 (w : BitVec 32) : (w ^^^ w <<< 16) >>> 16 = lo16 w ^^^ hi16 w := by
  rw [BitVec.ushiftRight_xor_distrib, BitVec.xor_comm]; rfl

/-- The carry-less product of two words, as two words, the low one first. -/
def mul32 (a b : BitVec 32) : BitVec 32 × BitVec 32 :=
  let p0 := cm16 (lo16 a) (lo16 b)
  let p1 := cm16 (hi16 a) (hi16 b)
  let m := cm16 (lo16 a ^^^ hi16 a) (lo16 b ^^^ hi16 b) ^^^ p0 ^^^ p1
  (p0 ^^^ m <<< 16, p1 ^^^ m >>> 16)

theorem lp_mul32 (a b : BitVec 32) : lp (mul32 a b).1 + X ^ 32 * lp (mul32 a b).2 = lp a * lp b := by
  have h2 : (2 : P) = 0 := CharTwo.two_eq_zero
  have e0 := lp_cm16 (low_lo16 a) (low_lo16 b)
  have e1 := lp_cm16 (low_hi16 a) (low_hi16 b)
  have em := lp_cm16 (low16_xor (low_lo16 a) (low_hi16 a)) (low16_xor (low_lo16 b) (low_hi16 b))
  rw [lp_xor, lp_xor] at em
  simp only [mul32]
  generalize cm16 (lo16 a) (lo16 b) = p0 at e0 ⊢
  generalize cm16 (hi16 a) (hi16 b) = p1 at e1 ⊢
  generalize cm16 (lo16 a ^^^ hi16 a) (lo16 b ^^^ hi16 b) = pm at em ⊢
  have es := lp_shift (pm ^^^ p0 ^^^ p1) (k := 16) (by decide)
  rw [lp_xor, lp_xor, em, e0, e1] at es
  rw [lp_xor, lp_xor, e0, e1, lp_lo_hi16 a, lp_lo_hi16 b]
  linear_combination es + (X ^ 16 * lp (lo16 a) * lp (lo16 b) + X ^ 16 * lp (hi16 a) * lp (hi16 b)) * h2

/-! ## 64-bit words, as two -/

/-- The carry-less product of `a₁ : a₀` and `b₁ : b₀`, four words, the low one first. -/
structure W4 where
  w0 : BitVec 32
  w1 : BitVec 32
  w2 : BitVec 32
  w3 : BitVec 32

def mulW4 (a1 a0 b1 b0 : BitVec 32) : W4 :=
  let p := mul32 a0 b0
  let q := mul32 a1 b1
  let r := mul32 (a0 ^^^ a1) (b0 ^^^ b1)
  ⟨p.1, p.2 ^^^ (r.1 ^^^ p.1 ^^^ q.1), q.1 ^^^ (r.2 ^^^ p.2 ^^^ q.2), q.2⟩

theorem mulW4_eq (a1 a0 b1 b0 : BitVec 32) :
    let w := mulW4 a1 a0 b1 b0
    polyMul (a1 ++ a0) (b1 ++ b0) = ((w.w3 ++ w.w2 : BitVec 64) ++ (w.w1 ++ w.w0 : BitVec 64) : BitVec 128) := by
  intro w
  apply lp_ext
  have h2 : (2 : P) = 0 := CharTwo.two_eq_zero
  have e0 := lp_mul32 a0 b0
  have e1 := lp_mul32 a1 b1
  have em := lp_mul32 (a0 ^^^ a1) (b0 ^^^ b1)
  rw [lp_xor, lp_xor] at em
  rw [lp_polyMul, lp_append a1 a0, lp_append b1 b0, lp_append (n := 64) (m := 64), lp_append w.w3 w.w2,
    lp_append w.w1 w.w0]
  simp only [w, mulW4, lp_xor]
  linear_combination (-(1 + X ^ 32)) * e0 - (X ^ 32 + X ^ 64) * e1 - X ^ 32 * em -
    (X ^ 32 * lp a0 * lp b0 + X ^ 32 * lp a1 * lp b1) * h2

/-! ## The reduction and the key, in words -/

def up32 (w : BitVec 32) : BitVec 32 := w >>> 1 ^^^ w >>> 2 ^^^ w >>> 7
def dn32 (w : BitVec 32) : BitVec 32 := w <<< 31 ^^^ w <<< 30 ^^^ w <<< 25

theorem shr_append (a b : BitVec 32) {k : Nat} (hk : k ≤ 32) :
    (a ++ b : BitVec 64) >>> k = (a >>> k) ++ (b >>> k ^^^ a <<< (32 - k)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_xor,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
  by_cases h1 : i < 32
  · by_cases h2 : k + i < 32
    · simp [h1, h2, show i < 32 - k by omega]
    · simp [h1, h2, show ¬ i < 32 - k by omega, BitVec.getLsbD_of_ge b (k + i) (by omega),
        show k + i - 32 = i - (32 - k) by omega]
  · simp [h1, show ¬ k + i < 32 by omega, show k + i - 32 = k + (i - 32) by omega]

theorem shl_append (a b : BitVec 32) {k : Nat} (hk : k ≤ 32) :
    (a ++ b : BitVec 64) <<< k = (a <<< k ^^^ b >>> (32 - k)) ++ (b <<< k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_xor,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft]
  by_cases h1 : i < 32
  · simp [h1, hi, show i - k < 32 by omega]
  · by_cases h2 : i - k < 32
    · simp [h1, hi, h2, show ¬ i < k by omega, show i - 32 < k by omega, show 32 - k + (i - 32) = i - k by omega,
        show i - 32 < 32 by omega]
    · simp [h1, hi, h2, show ¬ i < k by omega, show ¬ i - 32 < k by omega, show i - 32 < 32 by omega,
        show i - k - 32 = i - 32 - k by omega, BitVec.getLsbD_of_ge b (32 - k + (i - 32)) (by omega)]

theorem shl_append' (a b : BitVec 32) {k : Nat} (hk : 32 ≤ k) : (a ++ b : BitVec 64) <<< k = (b <<< (k - 32)) ++ 0#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_shiftLeft]
  by_cases h1 : i < 32
  · simp [h1, show i < k by omega]
  · by_cases h2 : i < k
    · simp [h1, h2, show i - 32 < k - 32 by omega]
    · simp [h1, hi, h2, show ¬ i - 32 < k - 32 by omega, show i - k < 32 by omega, show i - 32 < 32 by omega,
        show i - 32 - (k - 32) = i - k by omega]

theorem xor_append' (a b c d : BitVec 32) : (a ++ b : BitVec 64) ^^^ (c ++ d) = (a ^^^ c) ++ (b ^^^ d) :=
  BitVec.xor_append

theorem xor_shuffle (p q r a b c : BitVec 32) : p ^^^ a ^^^ (q ^^^ b) ^^^ (r ^^^ c) = p ^^^ q ^^^ r ^^^ (a ^^^ b ^^^ c) := by
  ac_rfl

theorem up_append (a b : BitVec 32) : up (a ++ b : BitVec 64) = up32 a ++ (up32 b ^^^ dn32 a) := by
  rw [up, shr_append a b (k := 1) (by decide), shr_append a b (k := 2) (by decide), shr_append a b (k := 7) (by decide),
    xor_append', xor_append', up32, up32, dn32]
  simp only [Nat.reduceSub]
  rw [xor_shuffle]

theorem dn_append (a b : BitVec 32) : dn (a ++ b : BitVec 64) = dn32 b ++ 0#32 := by
  rw [dn, shl_append' a b (by decide), shl_append' a b (by decide), shl_append' a b (by decide), xor_append', xor_append',
    dn32]
  simp

/-- The key's words, from `H`'s (`a₃` the first). -/
theorem keyW0_append (a3 a2 a1 a0 : BitVec 32) :
    keyW0 (a3 ++ a2 : BitVec 64) (a1 ++ a0 : BitVec 64) = (a1 <<< 1 ^^^ a0 >>> 31) ++ (a0 <<< 1 ^^^ a3 >>> 31) := by
  have h : (a3 ++ a2 : BitVec 64) >>> 63 = 0#32 ++ a3 >>> 31 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_ushiftRight]
    by_cases h : i < 32
    · simp [h, show ¬ 63 + i < 32 by omega, show 63 + i - 32 = 31 + i by omega]
    · simp [h, show ¬ 63 + i < 32 by omega, BitVec.getLsbD_of_ge a3 (63 + i - 32) (by omega)]
  rw [keyW0, shl_append a1 a0 (by decide), h, xor_append', BitVec.xor_zero]

theorem keyW1_append (a3 a2 a1 a0 : BitVec 32) :
    keyW1 (a3 ++ a2 : BitVec 64) (a1 ++ a0 : BitVec 64) =
      (a3 <<< 1 ^^^ a2 >>> 31 ^^^ dn32 (a3 >>> 31)) ++ (a2 <<< 1 ^^^ a1 >>> 31) := by
  have h : ∀ a b : BitVec 32, (a ++ b : BitVec 64) >>> 63 = 0#32 ++ a >>> 31 := by
    intro a b
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, BitVec.getLsbD_append, BitVec.getLsbD_ushiftRight]
    by_cases h : i < 32
    · simp [h, show ¬ 63 + i < 32 by omega, show 63 + i - 32 = 31 + i by omega]
    · simp [h, show ¬ 63 + i < 32 by omega, BitVec.getLsbD_of_ge a (63 + i - 32) (by omega)]
  rw [keyW1, shl_append a3 a2 (by decide), h a1 a0, h a3 a2, dn_append, xor_append', xor_append', BitVec.xor_zero,
    BitVec.xor_zero]

theorem vd0 (w : W4) : vdword ((w.w3 ++ w.w2 : BitVec 64) ++ (w.w1 ++ w.w0 : BitVec 64) : BitVec 128) 0 = w.w1 ++ w.w0 :=
  vdword_append_0 _ _
theorem vd1 (w : W4) : vdword ((w.w3 ++ w.w2 : BitVec 64) ++ (w.w1 ++ w.w0 : BitVec 64) : BitVec 128) 1 = w.w3 ++ w.w2 :=
  vdword_append_1 _ _

/-- `redW` in words: the product's eight, the low ones of `l`, and `c` the
middle one. -/
def redW4 (l h c : W4) : W4 :=
  let m0 := c.w0 ^^^ l.w0 ^^^ h.w0
  let m1 := c.w1 ^^^ l.w1 ^^^ h.w1
  let m2 := c.w2 ^^^ l.w2 ^^^ h.w2
  let m3 := c.w3 ^^^ l.w3 ^^^ h.w3
  let z2 := m0 ^^^ l.w2
  let z3 := m1 ^^^ l.w3 ^^^ dn32 l.w0
  ⟨h.w0 ^^^ m2 ^^^ l.w0 ^^^ (up32 l.w0 ^^^ dn32 l.w1), h.w1 ^^^ m3 ^^^ l.w1 ^^^ up32 l.w1 ^^^ dn32 z2,
    h.w2 ^^^ z2 ^^^ (up32 z2 ^^^ dn32 z3), h.w3 ^^^ z3 ^^^ up32 z3⟩

/-- The block's product in words: `y₃` first. -/
theorem mul_words32 (y3 y2 y1 y0 a3 a2 a1 a0 : BitVec 32) :
    let k0 := a0 <<< 1 ^^^ a3 >>> 31
    let k1 := a1 <<< 1 ^^^ a0 >>> 31
    let k2 := a2 <<< 1 ^^^ a1 >>> 31
    let k3 := a3 <<< 1 ^^^ a2 >>> 31 ^^^ dn32 (a3 >>> 31)
    let z := redW4 (mulW4 y1 y0 k1 k0) (mulW4 y3 y2 k3 k2) (mulW4 (y1 ^^^ y3) (y0 ^^^ y2) (k1 ^^^ k3) (k0 ^^^ k2))
    ((z.w3 ++ z.w2 : BitVec 64) ++ (z.w1 ++ z.w0 : BitVec 64) : BitVec 128) =
      Spec.Gcm.mul ((y3 ++ y2 : BitVec 64) ++ (y1 ++ y0 : BitVec 64) : BitVec 128)
        ((a3 ++ a2 : BitVec 64) ++ (a1 ++ a0 : BitVec 64) : BitVec 128) := by
  intro k0 k1 k2 k3 z
  have hl := mulW4_eq y1 y0 k1 k0
  have hh := mulW4_eq y3 y2 k3 k2
  have hc := mulW4_eq (y1 ^^^ y3) (y0 ^^^ y2) (k1 ^^^ k3) (k0 ^^^ k2)
  rw [← mul_words, mulW, keyW1_append, keyW0_append]
  rw [xor_append', xor_append', hl, hh, hc]
  simp only [z]
  generalize mulW4 y1 y0 k1 k0 = l
  generalize mulW4 y3 y2 k3 k2 = h
  generalize mulW4 (y1 ^^^ y3) (y0 ^^^ y2) (k1 ^^^ k3) (k0 ^^^ k2) = c
  simp only [redW, vdword_xor, vd0, vd1, dn_append, xor_append', up_append, redW4, BitVec.xor_zero]

end VG.Proof.Gcm.Spread
