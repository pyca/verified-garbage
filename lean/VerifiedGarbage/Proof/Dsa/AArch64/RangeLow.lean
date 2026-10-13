module

public import VerifiedGarbage.Proof.Dsa.AArch64.OrWords
public import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # The low boundary of DSA scalar and group-element ranges -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

def rangeLow (aboveOne : Bool) (x : BitVec 64) : BitVec 64 := if aboveOne then x >>> 1 else x

theorem rangeLow_zero (aboveOne : Bool) (x : BitVec 64) :
    rangeLow aboveOne x = 0 ↔ x.toNat ≤ (if aboveOne then 1 else 0) := by
  cases aboveOne
  · simp only [rangeLow, Bool.false_eq_true, ite_false, Nat.le_zero]
    exact ⟨fun h => congrArg BitVec.toNat h, fun h => BitVec.eq_of_toNat_eq h⟩
  · simp only [rangeLow, ite_true]
    rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight]
    change x.toNat / 2 = 0 ↔ x.toNat ≤ 1
    omega

/-- OR-ing all high limbs and testing the adjusted low limb characterizes
exactly the rejected lower interval: zero, or zero and one. -/
theorem rangeLow_words {mem : Mem} {B : Addr} {d w : Nat} (hw : 1 ≤ w) (aboveOne : Bool) :
    (rangeLow aboveOne (word mem B d) = 0 ∧
      ∀ i, 1 ≤ i → i < w → word mem B (d + 8 * i) = 0) ↔
      wv mem B d w ≤ (if aboveOne then 1 else 0) := by
  cases aboveOne
  · rw [rangeLow_zero]
    simp only [Bool.false_eq_true, ite_false, Nat.le_zero]
    rw [wv_eq_zero_iff]
    constructor
    · rintro ⟨h0, h⟩ i hi
      by_cases hz : i = 0
      · subst i
        simpa only [Nat.mul_zero, Nat.add_zero] using BitVec.eq_of_toNat_eq h0
      · exact h i (by omega) hi
    · intro h
      exact ⟨congrArg BitVec.toNat (by simpa using h 0 (by omega)), fun i _ hi => h i hi⟩
  · simp only [ite_true]
    rw [VG.Proof.RsaKeyGen.wv_le_one hw, VG.Proof.RsaKeyGen.and_m2_eq_zero, rangeLow_zero]
    rfl

/-- After the comparison: keep its borrow mask in `x11`, load the low limb
(optionally ignoring its least significant bit) into `x9`, and set up the
loop over the other limbs. -/
theorem rangeLow_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 1 ≤ w)
    (h7 : s.gpr .x7 = 0) (h12 : s.gpr .x12 = BitVec.ofNat 64 w) (aboveOne : Bool) :
    WP isa (.block (Impl.Rsa.AArch64.Crt.borrowMask ++
      ([mov .x11 .x15, ldh .x16 (sArr aX), ld .x9 .x16] : List Instr) ++
      (if aboveOne then [.lsr .x .x9 .x9 1] else []) ++
      ([next .x16, .subImm .x .x14 .x12 1] : List Instr))) s fun t =>
      t.gpr .x11 = mask (!s.c) ∧ t.gpr .x9 = rangeLow aboveOne (word s.mem B (slot w aX)) ∧
      t.gpr .x16 = off B (slot w aX + 8) ∧ t.gpr .x14 = BitVec.ofNat 64 (w - 1) ∧
      t.mem = s.mem ∧ Keep [.x4, .x9, .x11, .x14, .x15, .x16] s t := by
  have hx := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  refine WP.mono (WP.keep [.x4, .x9, .x11, .x14, .x15, .x16] (Q := fun t =>
    t.gpr .x11 = mask (!s.c) ∧ t.gpr .x9 = rangeLow aboveOne (word s.mem B (slot w aX)) ∧
      t.gpr .x16 = off B (slot w aX + 8) ∧ t.gpr .x14 = BitVec.ofNat 64 (w - 1) ∧ t.mem = s.mem) ?_
    (by cases aboveOne <;> decide) (by cases aboveOne <;> decide) (by cases aboveOne <;> decide +kernel))
    fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, hk⟩
  cases aboveOne <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, List.append_nil, rangeLow] <;>
    brun [Impl.Rsa.AArch64.Crt.borrowMask, h7, h12, csel_mask_not, hg.x0, hdr_enc (sArr_lt (show aX < 8 by decide)),
      hg.ld hZ (sArr_lt (show aX < 8 by decide)), hg.hdr.harr aX (by decide),
      hg.scr.ld (show slot w aX + 8 ≤ Z by omega), ofNat_sub_one hw]

end VG.Proof.Dsa.AArch64
