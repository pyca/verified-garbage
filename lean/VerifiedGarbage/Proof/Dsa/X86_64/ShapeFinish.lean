module

public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeFrame
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.X86_64.Operands

/-! # Digest-prefix selection and the public domain-check result -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev shapeFinish : List Instr :=
  [.mov .rax (.mem (Core.field .digestLen)), .mov .rdx (.mem (Core.field .digestPrefixLen)),
    .alu .cmp .rdx (.reg .rax), .cmov .b .rax (.reg .rdx),
    .store (Core.field .digestPrefixLen) .rax,
    .mov .rax (.mem (Core.field .mask)), .alu .test .rax (.reg .rax)]

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
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
    (hn : n < 2 ^ 64) (hq : q < 2 ^ 64)
    (hd : word s.mem B Field.digestLen.offset = BitVec.ofNat 64 n)
    (hp : word s.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 q)
    (hm : word s.mem B Field.mask.offset = mask valid) :
    WP isa (.block shapeFinish) s fun t =>
      word t.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 (min n q) ∧
      word t.mem B Field.mask.offset = mask valid ∧ t.zf = some (!valid) ∧
      Frm B shapeRanges s.mem t.mem ∧ Keep [.rax, .rdx] s t := by
  have hr : Field.mask.offset + 8 ≤ Z := Nat.le_trans (by decide) hZ
  have hf : Field.digestPrefixLen.offset + 8 ≤ Z := Nat.le_trans (by decide) hZ
  have hdw : Field.digestLen.offset + 8 ≤ Z := Nat.le_trans (by decide) hZ
  have hw (v : BitVec 64) : word (s.mem.writeW (off B Field.digestPrefixLen.offset) v) B Field.mask.offset =
      word s.mem B Field.mask.offset :=
    (writeW_outside _ _ _ (by decide)).word (Or.inr (by decide)) (by decide)
  refine WP.mono (WP.keep [.rax, .rdx] (Q := fun t =>
    t.mem = s.mem.writeW (off B Field.digestPrefixLen.offset) (BitVec.ofNat 64 (min n q)) ∧
    t.zf = some (!valid)) ?_ rfl) fun t ⟨⟨htm, htz⟩, hk⟩ => ?_
  · unfold shapeFinish
    by_cases hlt : q < n
    all_goals xrun [execCmov, eval, hlt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hq,
      State.ea, Core.field, hdi, fieldAddress, hs.ld hdw, hs.ld hf, hs.st hf, hs.ld hr,
      hd, hp, prefix_select hn hq, hw, hm, mask_test]
    · rw [Nat.min_eq_right (Nat.le_of_lt hlt)]
      exact ⟨rfl, mask_test valid⟩
    · rw [Nat.min_eq_left (Nat.le_of_not_gt hlt)]
      exact ⟨rfl, mask_test valid⟩
  · exact ⟨by rw [htm, word_writeW_self], by rw [htm, hw]; exact hm, htz,
      by rw [htm]; exact shape_store _ (Or.inr (Or.inl rfl)), hk⟩

end VG.Proof.Dsa.X86_64
