module

import Mathlib.Tactic.Convert
public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Dsa.AArch64.OrWords
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
public import VerifiedGarbage.Proof.Bignum.AArch64.Run
import VerifiedGarbage.Proof.RsaKeyGen.CandMath
public import Aesop.BuiltinRules

/-! ### `Dsa.AArch64.RangeLow`, which this module and modules that import it used -/

section

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
    omega_using []

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
      · exact h i (by omega_using [hz]) hi
    · intro h
      exact ⟨congrArg BitVec.toNat (by simpa using h 0 (by omega_using [hw])), fun i _ hi => h i hi⟩
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

end

end

/-! # Rejecting zero and one with a fixed-length limb scan -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem lowerScan_ok {s : State} {B : Addr} {Z w : Nat} {minv : BitVec 64}
    (hg : Good s B Z w minv) (hZ : slot w 8 ≤ Z) (hw : 2 ≤ w) (hw' : w < 2 ^ 31)
    (aboveOne : Bool) :
    WP isa (Checks.lowerScan aboveOne) s fun t =>
      (t.gpr .x15 = 0 ↔ wv s.mem B (slot w aX) w ≤ (if aboveOne then 1 else 0)) ∧
      t.mem = s.mem ∧ Keep mmRegs s t := by
  have hx := Nat.le_trans (slot_le (w := w) (show aX < 8 by decide)) hZ
  unfold Checks.lowerScan seqs
  refine WP.seq (WP.mono (WP.keep [.x12, .x16] (Q := fun u =>
    u.gpr .x12 = BitVec.ofNat 64 w ∧ u.gpr .x16 = off B (slot w aX) ∧ u.mem = s.mem)
    (by brun [hg.x0, hdr_enc (show sW < 32 by decide), hdr_enc (show sArr aX < 32 by decide),
      hg.hdr.hw, hg.hdr.harr aX (by decide), hg.ld hZ (show sW < 32 by decide), hg.ld hZ (show sArr aX < 32 by decide)])
    rfl rfl rfl) fun u ⟨⟨hu12, hu16, hum⟩, hku⟩ => ?_)
  refine WP.seq (WP.mono (rangeLow_ok (hg.scr.congr hku.wr) hu16 (by omega_using [hx]) aboveOne)
    fun v ⟨hv15, hvm, hkv⟩ => ?_)
  have hv12 := (hkv.gpr .x12 (by decide)).trans hu12
  have hv16 := (hkv.gpr .x16 (by decide)).trans hu16
  have hsub : BitVec.ofNat 64 w - (1#64) = BitVec.ofNat 64 (w - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    simp only [Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by decide)]
    omega_using [hw]
  refine WP.seq (WP.mono (WP.keep [.x16, .x14] (Q := fun z =>
    z.gpr .x16 = off B (slot w aX + 8) ∧ z.gpr .x14 = BitVec.ofNat 64 (w - 1) ∧ z.mem = v.mem)
    (by brun [hv16, hv12, hsub]) rfl rfl rfl) fun z ⟨⟨hz16, hz14, hzm⟩, hkz⟩ => ?_)
  have hk : Keep mmRegs s z := ((hku.trans hkv).trans hkz).mono (by decide)
  have hz15 : z.gpr .x15 = 0 ↔ rangeLow aboveOne (word s.mem B (slot w aX)) = 0 := by
    rw [hkz.gpr .x15 (by decide), hv15, hum]
  refine WP.mono (orWords_ok (hg.scr.congr hk.wr) hz16 hz14 hz15 (by omega_using [hw]) (by omega_using [hw']) (by omega_using [hx]))
    fun t ⟨ht, htm, hkt⟩ => ?_
  have hm : z.mem = s.mem := hzm.trans (hvm.trans hum)
  rw [hm] at ht
  have he : (∀ i < w - 1, word s.mem B (slot w aX + 8 + 8 * i) = 0) ↔
      ∀ i, 1 ≤ i → i < w → word s.mem B (slot w aX + 8 * i) = 0 := by
    constructor
    · intro h i hi hiw
      have hh := h (i - 1) (by omega_using [hw, hiw])
      convert hh using 2 <;> omega_using [hi]
    · intro h i hi
      have hh := h (i + 1) (by omega_using []) (by omega_using [hi])
      convert hh using 2 <;> omega_using []
  rw [he, rangeLow_words (by omega_using [hw]) aboveOne] at ht
  exact ⟨ht, htm.trans hm, (hk.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.AArch64
