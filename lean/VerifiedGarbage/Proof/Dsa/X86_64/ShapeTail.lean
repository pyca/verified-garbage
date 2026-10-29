module

public import VerifiedGarbage.Proof.Dsa.X86_64.OddCheck
public import VerifiedGarbage.Proof.Dsa.X86_64.ShapeFrame

import VerifiedGarbage.Proof.Dsa.X86_64.Masks
import VerifiedGarbage.Proof.Dsa.X86_64.Operands
/-! # Composition of domain masks, parity, and digest-prefix selection -/

-- Formerly `VerifiedGarbage/Proof/Dsa/X86_64/ShapeFinish.lean`, which only this module imported.
section

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
end

end

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

abbrev shapeTail : List Instr := Checks.accumulate ++ oddCheck ++ shapeFinish

theorem shapeTail_ok {s : State} {B pp qp : Addr} {Z n width : Nat} {p q : List Byte}
    {pLast qLast : Byte} {valid sizes : Bool}
    (hs : Scr s B Z) (hdi : s.gpr .rdi = B) (hZ : pWorkspace ≤ Z)
    (hpp : word s.mem B Field.p.offset = pp) (hqp : word s.mem B Field.q.offset = qp)
    (hpl : word s.mem B Field.pLen.offset = BitVec.ofNat 64 p.length)
    (hql : word s.mem B Field.qLen.offset = BitVec.ofNat 64 q.length)
    (hps : Src s B Z pp p) (hqs : Src s B Z qp q)
    (hp1 : 0 < p.length) (hp64 : p.length < 2 ^ 64) (hq1 : 0 < q.length) (hq64 : q.length < 2 ^ 64)
    (hplast : p[p.length - 1] = pLast) (hqlast : q[q.length - 1] = qLast)
    (hn : n < 2 ^ 64) (hw : width < 2 ^ 64)
    (hd : word s.mem B Field.digestLen.offset = BitVec.ofNat 64 n)
    (hwidth : word s.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 width)
    (ha : s.gpr .rax = mask sizes) (hm : word s.mem B Field.mask.offset = mask valid) :
    WP isa (.block shapeTail) s fun t =>
      word t.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 (min n width) ∧
      word t.mem B Field.mask.offset = mask (decide (pLast.toNat % 2 = 1 ∧ qLast.toNat % 2 = 1) && (sizes && valid)) ∧
      t.zf = some (!(decide (pLast.toNat % 2 = 1 ∧ qLast.toNat % 2 = 1) && (sizes && valid))) ∧
      Frm B shapeRanges s.mem t.mem ∧ Keep mmRegs s t := by
  unfold shapeTail
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (accumulate_ok hs hdi hZ ha hm) fun u ⟨hum, hfu, hku⟩ => ?_
  have huf := shape_outside hfu (Or.inr (Or.inr rfl))
  have hups := shape_source huf hku (Nat.le_trans (by decide) hZ) hps
  have huqs := shape_source huf hku (Nat.le_trans (by decide) hZ) hqs
  have hudi := (hku.gpr (show Reg.rdi ∉ _ by decide)).trans hdi
  have hpidx : p.length - 1 < p.length := by omega
  have hqidx : q.length - 1 < q.length := by omega
  rw [WP.block_append_iff]
  refine WP.mono (oddCheck_ok (hs.congr hku.2.2) hudi hZ
    ((shape_field huf .p (by decide) (by decide)).trans hpp)
    ((shape_field huf .q (by decide) (by decide)).trans hqp)
    ((shape_field huf .pLen (by decide) (by decide)).trans hpl)
    ((shape_field huf .qLen (by decide) (by decide)).trans hql)
    hp1 hp64 hq1 hq64 (hups.rd _ hpidx) (huqs.rd _ hqidx)
    ((hups.val _ hpidx).trans hplast) ((huqs.val _ hqidx).trans hqlast) hum)
    fun v ⟨hvm, hfv, hkv⟩ => ?_
  have hvf := shape_outside hfv (Or.inr (Or.inr rfl))
  have hksv := hku.trans hkv
  have hvdi := (hksv.gpr (show Reg.rdi ∉ _ by decide)).trans hdi
  have hvwidth : word v.mem B Field.digestPrefixLen.offset = BitVec.ofNat 64 width :=
    (hfv.word (Or.inl (by decide)) (by decide)).trans
      ((hfu.word (Or.inl (by decide)) (by decide)).trans hwidth)
  refine WP.mono (shapeFinish_ok (hs.congr hksv.2.2) hvdi hZ hn hw
    ((shape_field (huf.trans hvf) .digestLen (by decide) (by decide)).trans hd)
    hvwidth hvm) fun t ⟨htw, htm, htz, hft, hkt⟩ => ?_
  exact ⟨htw, htm, htz, (huf.trans hvf).trans hft, (hksv.trans hkt).mono (by decide)⟩

end VG.Proof.Dsa.X86_64
