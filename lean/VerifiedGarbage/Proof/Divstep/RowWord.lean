module

import VerifiedGarbage.Proof.Framework.Omega

/-!
# A word of a signed linear combination of multiword numbers

`u X + v Y` for signed words `u`, `v` and unsigned multiword `X`, `Y`, a
word at a time with a signed carry: each word's products as signed 128-bit
numbers (`umulh` less the word where its coefficient is negative), their
low words and the carry summed with carries out, and the next carry their
high words plus those carries plus the carry's sign word (`rowWord`).
-/

@[expose] public section

namespace VG.Proof.Divstep

/-- A word's sign mask: `0 - (x >>> 63)`. -/
theorem signMask_eq (x : BitVec 64) :
    0#64 - (x >>> 63) = if x.toNat < 2 ^ 63 then 0#64 else BitVec.allOnes 64 := by
  have hx := x.isLt
  have e : (x >>> 63).toNat = x.toNat / 2 ^ 63 := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, e]
  split
  · rw [show x.toNat / 2 ^ 63 = 0 by omega]; rfl
  · rw [show x.toNat / 2 ^ 63 = 1 by omega]; rfl

theorem and_mask (a x : BitVec 64) :
    a &&& (if x.toNat < 2 ^ 63 then 0#64 else BitVec.allOnes 64) = if x.toNat < 2 ^ 63 then 0#64 else a := by
  split
  · exact BitVec.and_zero
  · exact BitVec.and_allOnes

theorem toInt_cond (x : BitVec 64) : x.toInt = if x.toNat < 2 ^ 63 then (x.toNat : Int) else x.toNat - 2 ^ 64 := by
  rw [BitVec.toInt_eq_toNat_cond]
  by_cases h : x.toNat < 2 ^ 63
  · rw [ite_eq_left (by omega : 2 * x.toNat < 2 ^ 64), ite_eq_left h]
  · rw [ite_eq_right (by omega : ¬ 2 * x.toNat < 2 ^ 64), ite_eq_right h]
    have : ((2 ^ 64 : Nat) : Int) = 2 ^ 64 := rfl
    omega

theorem decide_toNat_div (x : Nat) (h : x < 2 ^ 65) : (decide (2 ^ 64 ≤ x)).toNat = x / 2 ^ 64 := by
  by_cases h' : 2 ^ 64 ≤ x <;> simp [h'] <;> omega

theorem rowWord (cu cv a b c : BitVec 64) (hb : cu.toInt.natAbs + cv.toInt.natAbs ≤ 2 ^ 62)
    (hc : c.toInt.natAbs ≤ 2 ^ 62) :
    let lo1 := cu * a
    let hi1 := BitVec.ofNat 64 (cu.toNat * a.toNat / 2 ^ 64) - (a &&& (0#64 - (cu >>> 63)))
    let lo2 := cv * b
    let hi2 := BitVec.ofNat 64 (cv.toNat * b.toNat / 2 ^ 64) - (b &&& (0#64 - (cv >>> 63)))
    let s1 := lo1 + lo2
    let lo := s1 + c
    let c' := hi1 + hi2 + BitVec.ofNat 64 (decide (2 ^ 64 ≤ lo1.toNat + lo2.toNat)).toNat +
      ~~~((c >>> 63) - 1#64) + BitVec.ofNat 64 (decide (2 ^ 64 ≤ s1.toNat + c.toNat)).toNat
    (lo.toNat : Int) + 2 ^ 64 * c'.toInt = cu.toInt * a.toNat + cv.toInt * b.toNat + c.toInt ∧
      c'.toInt.natAbs ≤ 2 ^ 62 := by
  intro lo1 hi1 lo2 hi2 s1 lo c'
  have ha := a.isLt; have hb' := b.isLt; have hcu := cu.isLt; have hcv := cv.isLt; have hcl := c.isLt
  obtain ⟨P, hP⟩ : ∃ P, P = cu.toNat * a.toNat := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = cv.toNat * b.toNat := ⟨_, rfl⟩
  -- The masked words as atoms.
  obtain ⟨Eu, hEu⟩ : ∃ E, E = (a &&& (0#64 - (cu >>> 63))).toNat := ⟨_, rfl⟩
  obtain ⟨Ev, hEv⟩ : ∃ E, E = (b &&& (0#64 - (cv >>> 63))).toNat := ⟨_, rfl⟩
  have eu : (Eu : Int) = if cu.toNat < 2 ^ 63 then 0 else a.toNat := by
    rw [hEu, signMask_eq, and_mask]; split <;> simp
  have ev : (Ev : Int) = if cv.toNat < 2 ^ 63 then 0 else b.toNat := by
    rw [hEv, signMask_eq, and_mask]; split <;> simp
  have eu' : Eu < 2 ^ 64 := by rw [hEu]; exact BitVec.isLt _
  have ev' : Ev < 2 ^ 64 := by rw [hEv]; exact BitVec.isLt _
  have pu : cu.toInt * (a.toNat : Int) = P - 2 ^ 64 * Eu := by
    rw [toInt_cond, hP, eu]; split <;> push_cast <;> grind
  have pv : cv.toInt * (b.toNat : Int) = Q - 2 ^ 64 * Ev := by
    rw [toInt_cond, hQ, ev]; split <;> push_cast <;> grind
  have bnd : (cu.toInt * a.toNat + cv.toInt * b.toNat + c.toInt).natAbs ≤ 2 ^ 62 * (2 ^ 64 - 1) + 2 ^ 62 := by
    have e1 : (cu.toInt * a.toNat).natAbs ≤ cu.toInt.natAbs * (2 ^ 64 - 1) := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]; exact Nat.mul_le_mul_left _ (by omega)
    have e2 : (cv.toInt * b.toNat).natAbs ≤ cv.toInt.natAbs * (2 ^ 64 - 1) := by
      rw [Int.natAbs_mul, Int.natAbs_natCast]; exact Nat.mul_le_mul_left _ (by omega)
    have e3 : cu.toInt.natAbs * (2 ^ 64 - 1) + cv.toInt.natAbs * (2 ^ 64 - 1) ≤ 2 ^ 62 * (2 ^ 64 - 1) := by
      rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ hb
    omega
  -- The carry's sign.
  obtain ⟨ec, hec⟩ : ∃ e, e = c.toNat / 2 ^ 63 := ⟨_, rfl⟩
  have tc : c.toInt = c.toNat - 2 ^ 64 * ec := by
    rw [toInt_cond, hec]
    split
    · rw [Nat.div_eq_of_lt (by omega)]; omega
    · rw [show c.toNat / 2 ^ 63 = 1 by omega]; omega
  have hm : (c >>> 63).toNat = ec := by rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hec]
  have hl1 : lo1.toNat = P % 2 ^ 64 := by simp only [lo1, BitVec.toNat_mul, hP]
  have hl2 : lo2.toNat = Q % 2 ^ 64 := by simp only [lo2, BitVec.toNat_mul, hQ]
  have hs1 : s1.toNat = (lo1.toNat + lo2.toNat) % 2 ^ 64 := by simp only [s1, BitVec.toNat_add]
  have hlo : lo.toNat = (s1.toNat + c.toNat) % 2 ^ 64 := by simp only [lo, BitVec.toNat_add]
  have d1 := decide_toNat_div (lo1.toNat + lo2.toNat) (by omega)
  have d2 := decide_toNat_div (s1.toNat + c.toNat) (by omega)
  -- The carry word as an integer modulo `2^64`.
  obtain ⟨K, hK⟩ : ∃ K : Int, K = ((P / 2 ^ 64 : Nat) - (Eu : Int)) + ((Q / 2 ^ 64 : Nat) - (Ev : Int)) +
      ((lo1.toNat + lo2.toNat) / 2 ^ 64 : Nat) - (ec : Int) + ((s1.toNat + c.toNat) / 2 ^ 64 : Nat) := ⟨_, rfl⟩
  have hPq : P / 2 ^ 64 < 2 ^ 64 := by rw [hP]; exact Nat.div_lt_of_lt_mul (Nat.mul_lt_mul'' hcu ha)
  have hQq : Q / 2 ^ 64 < 2 ^ 64 := by rw [hQ]; exact Nat.div_lt_of_lt_mul (Nat.mul_lt_mul'' hcv hb')
  have he1 : ec ≤ 1 := by omega_using [hec, hcl]
  have hd1 : (lo1.toNat + lo2.toNat) / 2 ^ 64 ≤ 1 := by have := lo1.isLt; have := lo2.isLt; omega_using [this]
  have hc' : c' = BitVec.ofInt 64 K := by
    have os : ∀ x y : Int, BitVec.ofInt 64 (x - y) = BitVec.ofInt 64 x - BitVec.ofInt 64 y := fun x y => by
      rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]
    have on : ∀ x : Nat, BitVec.ofNat 64 x = BitVec.ofInt 64 (x : Int) := fun x => (BitVec.ofInt_natCast 64 x).symm
    have m1 : a &&& (0#64 - (cu >>> 63)) = BitVec.ofInt 64 (Eu : Int) := by
      rw [← on, hEu, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have m2 : b &&& (0#64 - (cv >>> 63)) = BitVec.ofInt 64 (Ev : Int) := by
      rw [← on, hEv, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have m3 : ~~~((c >>> 63) - 1#64) = BitVec.ofInt 64 (-(ec : Int)) := by
      rw [BitVec.ofInt_neg, ← on, ← hm, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.not_eq_neg_add,
        BitVec.neg_sub]
      grind
    have e1 : hi1 = BitVec.ofInt 64 ((P / 2 ^ 64 : Nat) - (Eu : Int)) := by
      rw [os, ← on, ← m1, hP]
    have e2 : hi2 = BitVec.ofInt 64 ((Q / 2 ^ 64 : Nat) - (Ev : Int)) := by
      rw [os, ← on, ← m2, hQ]
    simp only [c', e1, e2, m3]
    simp only [d1, d2, on, ← BitVec.ofInt_add]
    rw [hK]
    congr 1
  have key : (cu.toInt * a.toNat + cv.toInt * b.toNat + c.toInt) = (lo.toNat : Int) + 2 ^ 64 * K := by
    rw [pu, pv, tc, hK, hlo, hs1, hl1, hl2]; omega
  have kb : -(2 ^ 62) ≤ K ∧ K ≤ 2 ^ 62 := by
    have := lo.isLt
    rw [key] at bnd; omega
  have tk : c'.toInt = K := by
    rw [hc', BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le (by omega) (by omega)
  rw [tk, ← key]
  exact ⟨rfl, by omega⟩


end VG.Proof.Divstep
