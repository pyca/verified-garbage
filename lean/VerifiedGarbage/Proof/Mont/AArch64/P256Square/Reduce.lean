import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Product

namespace VG.Proof.Mont.AArch64.P256Square
open VG VG.AArch64 VG.Impl.Mont.AArch64.P256Square
open VG.Proof.Ed25519.Word64
open VG.Proof.Ed25519.AArch64

abbrev lowValue (s : State) := val4 (s.gpr .x8) (s.gpr .x9) (s.gpr .x10) (s.gpr .x11)
abbrev highValue (s : State) := val4 (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15)
abbrev reduceClob : List Reg := [.x1,.x2,.x3,.x6,.x8,.x9,.x10,.x11]

private theorem reduce_false_ok (s : State) (hz : s.gpr .x7 = 0)
    (hlo : s.gpr .x1 = s.gpr .x8 <<< 32) (hhi : s.gpr .x2 = s.gpr .x8 >>> 32) :
    WP isa (.block (reduceCode false)) s fun t =>
      B*lowValue t = lowValue s + (s.gpr .x8).toNat*p ∧
      (false = true → t.gpr .x1 = t.gpr .x8 <<< 32 ∧ t.gpr .x2 = t.gpr .x8 >>> 32) ∧
      Keeps reduceClob s t := by
  dsimp only [lowValue, reduceClob]
  apply WP.of_runBlock
  simp only [reduceCode, Bool.false_eq_true, ite_false, ite_true, List.append_nil,
      List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
      BitVec.setWidth_eq, reduceCtorEq, hz, hlo, hhi,
      Option.some.injEq, exists_eq_left']
  refine ⟨?_, by simp, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · have h := reduceWords_value (s.gpr .x8) (s.gpr .x9) (s.gpr .x10) (s.gpr .x11)
    dsimp only [lowValue, reduceWords, value4, add4, addCarry, carryOut, Size.bits] at h ⊢
    exact h
  · reg_keeps

private theorem reduce_true_ok (s : State) (hz : s.gpr .x7 = 0)
    (hlo : s.gpr .x1 = s.gpr .x8 <<< 32) (hhi : s.gpr .x2 = s.gpr .x8 >>> 32) :
    WP isa (.block (reduceCode true)) s fun t =>
      B*lowValue t = lowValue s + (s.gpr .x8).toNat*p ∧
      (true = true → t.gpr .x1 = t.gpr .x8 <<< 32 ∧ t.gpr .x2 = t.gpr .x8 >>> 32) ∧
      Keeps reduceClob s t := by
  dsimp only [lowValue, reduceClob]
  apply WP.of_runBlock
  simp only [reduceCode, ite_false, ite_true, 
      List.cons_append, List.nil_append,
      runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
      RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
      BitVec.setWidth_eq, reduceCtorEq, hz, hlo, hhi,
      show 32 < Size.x.bits by decide,
      Option.some.injEq, exists_eq_left']
  refine ⟨?_, by simp, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · have h := reduceWords_value (s.gpr .x8) (s.gpr .x9) (s.gpr .x10) (s.gpr .x11)
    dsimp only [lowValue, reduceWords, value4, add4, addCarry, carryOut, Size.bits] at h ⊢
    exact h
  · reg_keeps

theorem reduce_ok (s : State) (next : Bool) (hz : s.gpr .x7 = 0)
    (hlo : s.gpr .x1 = s.gpr .x8 <<< 32) (hhi : s.gpr .x2 = s.gpr .x8 >>> 32) :
    WP isa (.block (reduceCode next)) s fun t =>
      B*lowValue t = lowValue s + (s.gpr .x8).toNat*p ∧
      (next = true → t.gpr .x1 = t.gpr .x8 <<< 32 ∧ t.gpr .x2 = t.gpr .x8 >>> 32) ∧
      Keeps reduceClob s t := by
  cases next
  · exact reduce_false_ok s hz hlo hhi
  · exact reduce_true_ok s hz hlo hhi

theorem finish_ok (s : State) (hz : s.gpr .x7 = 0) :
    WP isa (.block finishCode) s fun t =>
      lowValue t + R*(t.gpr .x12).toNat = lowValue s + highValue s ∧
      Keeps [.x8,.x9,.x10,.x11,.x12] s t := by
  apply WP.of_runBlock
  simp only [finishCode, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, ite_true, ite_false, reduceCtorEq, hz,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
      by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
      by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
      by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · have h := add4_value (s.gpr .x8) (s.gpr .x9) (s.gpr .x10) (s.gpr .x11)
      (s.gpr .x12) (s.gpr .x13) (s.gpr .x14) (s.gpr .x15)
    dsimp only [lowValue, highValue, value4, add4, addCarry, carryOut, Size.bits] at h ⊢
    have hc (c : Bool) : ((0 : BitVec 64) + 0 + BitVec.ofNat 64 c.toNat).toNat = c.toNat := by
      cases c <;> rfl
    simp only [hc]
    exact h
  · reg_keeps

theorem reduceFour_ok (s : State) (hz : s.gpr .x7 = 0)
    (hlo : s.gpr .x1 = s.gpr .x8 <<< 32) (hhi : s.gpr .x2 = s.gpr .x8 >>> 32) :
    WP isa (.block (reduceCode true ++ reduceCode true ++ reduceCode true ++ reduceCode false)) s fun t =>
      (∃ u < R, R*lowValue t = lowValue s + u*p) ∧ Keeps reduceClob s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok s true hz hlo hhi) fun s₁ ⟨e₁, h₁, k₁⟩ => ?_
  obtain ⟨lo₁, hi₁⟩ := h₁ rfl
  have z₁ : s₁.gpr .x7 = 0 := (k₁.gpr _ (by decide)).trans hz
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok s₁ true z₁ lo₁ hi₁) fun s₂ ⟨e₂, h₂, k₂⟩ => ?_
  obtain ⟨lo₂, hi₂⟩ := h₂ rfl
  have z₂ : s₂.gpr .x7 = 0 := (k₂.gpr _ (by decide)).trans z₁
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok s₂ true z₂ lo₂ hi₂) fun s₃ ⟨e₃, h₃, k₃⟩ => ?_
  obtain ⟨lo₃, hi₃⟩ := h₃ rfl
  have z₃ : s₃.gpr .x7 = 0 := (k₃.gpr _ (by decide)).trans z₂
  refine WP.mono (reduce_ok s₃ false z₃ lo₃ hi₃) fun t ⟨e₄, _, k₄⟩ => ?_
  refine ⟨⟨val4 (s.gpr .x8) (s₁.gpr .x8) (s₂.gpr .x8) (s₃.gpr .x8),
    val4_lt _ _ _ _, ?_⟩, k₁.trans (k₂.trans (k₃.trans k₄))⟩
  have h := reduction_four (hi := 0) e₁ e₂ e₃ e₄ (rfl : lowValue t = lowValue t + 0)
  simpa only [Nat.mul_zero, Nat.add_zero, val4] using h

end VG.Proof.Mont.AArch64.P256Square
