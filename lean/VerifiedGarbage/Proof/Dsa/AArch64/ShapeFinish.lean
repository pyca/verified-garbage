module

public import VerifiedGarbage.Proof.Dsa.AArch64.ShapeFrame
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

/-! # Digest-prefix selection and the public domain-check result -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev shapeFinish : List Instr :=
  [Core.field .x3 .digestLen, Core.field .x5 .digestPrefixLen,
    .subs .x .x4 .x3 .x5, .csel .x .x3 .x5 .x3,
    .str .x .x3 .x0 Field.digestPrefixLen.offset, Core.field .x3 .mask]

theorem prefix_select {n q : Nat} (hn : n < 2 ^ 64) (hq : q < 2 ^ 64) :
    (if decide (2 ^ 64 ≤ (BitVec.ofNat 64 n).toNat + (~~~(BitVec.ofNat 64 q)).toNat + (true).toNat) then
      BitVec.ofNat 64 q else BitVec.ofNat 64 n) = BitVec.ofNat 64 (min n q) := by
  have hnot : (~~~(BitVec.ofNat 64 q)).toNat = 2 ^ 64 - 1 - q := by
    rw [BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq]
  rw [hnot, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Bool.toNat_true]
  by_cases h : q ≤ n
  · rw [decide_eq_true (by omega), Nat.min_eq_right h]; rfl
  · rw [decide_eq_false (by omega), Nat.min_eq_left (by omega)]; rfl

theorem shapeFinish_ok {s : State} {B : Addr} {Z n q : Nat} {valid : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (hn : n < 2 ^ 64) (hq : q < 2 ^ 64)
    (hd : word s.mem B Field.digestLen.offset = BitVec.ofNat 64 n)
    (hp : word s.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 q)
    (hm : word s.mem B Field.mask.offset = mask valid) :
    WP isa (.block shapeFinish) s fun t =>
      word t.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 (min n q) ∧
      word t.mem B Field.mask.offset = mask valid ∧ t.gpr .x3 = mask valid ∧
      Frm B shapeRanges s.mem t.mem ∧ Keep [.x3, .x4, .x5] s t := by
  have hr : Field.mask.offset + 8 ≤ Z := Nat.le_trans (by decide) hZ
  have hf : Field.digestPrefixLen.offset + 8 ≤ Z := Nat.le_trans (by decide) hZ
  have hdw : Field.digestLen.offset + 8 ≤ Z := Nat.le_trans (by decide) hZ
  have hw (v : BitVec 64) : word (s.mem.writeW (off B Field.digestPrefixLen.offset) v) B Field.mask.offset =
      word s.mem B Field.mask.offset :=
    (writeW_outside _ _ _ (by decide)).word (Or.inr (by decide)) (by decide)
  have hw' (v : BitVec 64) : (s.mem.writeW (off B Field.digestPrefixLen.offset) v).readW
      (off B Field.mask.offset) 64 = mask valid := (hw v).trans hm
  have hd' : s.mem.readW (off B Field.digestLen.offset) 64 = BitVec.ofNat 64 n := hd
  have hp' : s.mem.readW (off B Field.digestPrefixLen.offset) 64 = BitVec.ofNat 64 q := hp
  refine WP.mono (WP.keep [.x3, .x4, .x5] (Q := fun t =>
    t.mem = s.mem.writeW (off B Field.digestPrefixLen.offset) (BitVec.ofNat 64 (min n q)) ∧
    t.gpr .x3 = mask valid) ?_ (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨htm, ht3⟩, hk⟩ => ?_
  · unfold shapeFinish Core.field
    brun [hdi, field_enc, hs.ld hdw, hs.ld hf, hs.st hf, hs.ld hr, hd', hp', prefix_select hn hq, hw']
  · exact ⟨by rw [htm, word_writeW_self], by rw [htm, hw]; exact hm, ht3,
      by rw [htm]; exact shape_store _ (Or.inr (Or.inl rfl)), hk⟩

end VG.Proof.Dsa.AArch64
