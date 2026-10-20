module

public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeFrame
import Mathlib.Order.Lattice
import VerifiedGarbage.Proof.Dsa.AArch64.Operands
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Framework.Contract

/-! # Digest-prefix selection and the public domain-check result -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev shapeFinish : List Instr :=
  [Core.field .x3 .digestLen, Core.field .x2 .digestPrefixLen,
    .subs .x .x4 .x2 .x3, .csel .x .x3 .x3 .x2,
    .str .x .x3 .x0 Field.digestPrefixLen.offset, Core.field .x3 .mask]

theorem prefix_select {n q : Nat} (hn : n < 2 ^ 64) (hq : q < 2 ^ 64) :
    (if decide ((BitVec.ofNat 64 q).toNat < (BitVec.ofNat 64 n).toNat) then
      BitVec.ofNat 64 q else BitVec.ofNat 64 n) = BitVec.ofNat 64 (min n q) := by
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hq]
  split <;> rename_i h
  · rw [Nat.min_eq_right (Nat.le_of_lt (of_decide_eq_true h))]
  · rw [Nat.min_eq_left (Nat.le_of_not_gt (by simpa only [decide_eq_true_eq] using h))]

theorem mask_test (valid : Bool) : (mask valid &&& mask valid == 0#64) = !valid := by
  cases valid <;> decide

theorem shapeFinish_ok {s : State} {B : Addr} {Z n q : Nat} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (hn : n < 2 ^ 64) (hq : q < 2 ^ 64)
    (hd : word s.mem B Field.digestLen.offset = BitVec.ofNat 64 n)
    (hp : word s.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 q)
    (hm : word s.mem B Field.mask.offset = mask valid) :
    WP isa (.block shapeFinish) s fun t =>
      word t.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 (min n q) ∧
      word t.mem B Field.mask.offset = mask valid ∧ (t.gpr .x3 == (0#64)) = !valid ∧
      Frm B shapeRanges s.mem t.mem ∧ Keep [.x3, .x2, .x4] s t := by
  have hr : Field.mask.offset + 8 ≤ Z := Nat.le_trans (by decide) hZ
  have hf : Field.digestPrefixLen.offset + 8 ≤ Z := Nat.le_trans (by decide) hZ
  have hdw : Field.digestLen.offset + 8 ≤ Z := Nat.le_trans (by decide) hZ
  have hw (v : BitVec 64) : word (s.mem.writeW (off B Field.digestPrefixLen.offset) v) B Field.mask.offset =
      word s.mem B Field.mask.offset :=
    (writeW_outside _ _ _ (by decide)).word (Or.inr (by decide)) (by decide)
  refine WP.mono (WP.keep [.x3, .x2, .x4] (Q := fun t =>
    t.mem = s.mem.writeW (off B Field.digestPrefixLen.offset) (BitVec.ofNat 64 (min n q)) ∧
    (t.gpr .x3 == (0#64)) = !valid) ?_ rfl rfl rfl) fun t ⟨⟨htm, htz⟩, hk⟩ => ?_
  · unfold shapeFinish
    have hcarry : decide (2 ^ 64 ≤ (BitVec.ofNat 64 q).toNat + (~~~BitVec.ofNat 64 n).toNat + 1) = decide (n ≤ q) := by
      simp only [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hq]
      exact decide_eq_decide.mpr (by omega)
    have hsel : (if decide (n ≤ q) then BitVec.ofNat 64 n else BitVec.ofNat 64 q) = BitVec.ofNat 64 (min n q) := by
      by_cases h : n ≤ q <;> simp [h, Nat.min_def]
    brun [Core.field, hdi, field_enc .digestLen, field_enc .digestPrefixLen, field_enc .mask,
      hs.ld hdw, hs.ld hf, hs.st hf, hs.ld hr, hd, hp, hcarry, hsel, hw, hm]
    simp only [Bool.toNat_true, hcarry, hsel]
    exact ⟨True.intro, by cases valid <;> rfl⟩
  · exact ⟨by rw [htm, word_writeW_self], by rw [htm, hw]; exact hm, htz,
      by rw [htm]; exact shape_store _ (Or.inr (Or.inl rfl)), hk⟩

end VG.Proof.Dsa.AArch64
