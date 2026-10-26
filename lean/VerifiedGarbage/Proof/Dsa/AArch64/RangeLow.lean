module
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.RsaKeyGen.CandMath
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Framework.Contract

/-! # The low boundary of DSA scalar and group-element ranges -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
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

/-- Load the low limb and optionally ignore its least significant bit. -/
theorem rangeLow_ok {s : State} {B : Addr} {Z e : Nat}
    (hs : Scr s B Z) (hbx : s.gpr .x16 = off B e) (he : e + 8 ≤ Z) (aboveOne : Bool) :
    WP isa (.block (([ld .x15 .x16] : List Instr) ++
      (if aboveOne then [.lsr .x .x15 .x15 1] else []))) s fun t =>
      t.gpr .x15 = rangeLow aboveOne (word s.mem B e) ∧
      t.mem = s.mem ∧ Keep [.x15] s t := by
  refine WP.mono (WP.keep [.x15] (Q := fun t =>
    t.gpr .x15 = rangeLow aboveOne (word s.mem B e) ∧ t.mem = s.mem) ?_ ?_ ?_ ?_)
    fun t ⟨⟨hv, hm⟩, hk⟩ => ⟨hv, hm, hk⟩
  · cases aboveOne <;> simp only [Bool.false_eq_true, ite_false, ite_true, List.append_nil, List.cons_append, List.nil_append, rangeLow]
    all_goals brun [hbx, hs.ld he]
  all_goals cases aboveOne <;> rfl

end VG.Proof.Dsa.AArch64
