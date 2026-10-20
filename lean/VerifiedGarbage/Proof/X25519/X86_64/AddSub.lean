module

public import VerifiedGarbage.Proof.X25519.X86_64.Ops
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec

/-!
# X25519 on x86-64: addition and subtraction
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

theorem ld_sc {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 4096) :
    InRegions (s.rd ++ s.wr) (off base d) 8 :=
  ⟨_, List.mem_append_right _ hs.wr, contains_sc hd⟩

/-- The sum of `[a]` and `[b]` into `r8–r11`, and `38 ×` its carry into `rax`. -/
theorem addPre_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat} (ha : Slot a)
    (hb : Slot b) :
    WP isa (.block [.mov .r8 (.mem (sc a)), .alu .add .r8 (.mem (sc b)),
      .mov .r9 (.mem (sc (a + 8))), .alu .adc .r9 (.mem (sc (b + 8))),
      .mov .r10 (.mem (sc (a + 16))), .alu .adc .r10 (.mem (sc (b + 16))),
      .mov .r11 (.mem (sc (a + 24))), .alu .adc .r11 (.mem (sc (b + 24))),
      .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)]) s fun s' =>
      ∃ c : Nat, c ≤ 1 ∧
        val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + 2 ^ 256 * c =
          fe s.mem base a + fe s.mem base b ∧
        (s'.gpr .rax).toNat = 38 * c ∧ Keeps [.r8, .r9, .r10, .r11, .rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load64,
    ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, hs.rdi, ld_sc hs (d := a) (by omega),
    ld_sc hs (d := b) (by omega), ld_sc hs (d := a + 8) (by omega),
    ld_sc hs (d := b + 8) (by omega), ld_sc hs (d := a + 16) (by omega),
    ld_sc hs (d := b + 16) (by omega), ld_sc hs (d := a + 24) (by omega),
    ld_sc hs (d := b + 24) (by omega), ite_true, ite_false, reduceCtorEq, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨_, Bool.toNat_le _, ?_, mask38 _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  · exact chain_add _ _ _ _ _ _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2, ite_false]

/-- `[o] = [a] + [b]`. -/
theorem add_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (add o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a + F s.mem base b := by
  rw [show add o a b = [.mov .r8 (.mem (sc a)), .alu .add .r8 (.mem (sc b)),
      .mov .r9 (.mem (sc (a + 8))), .alu .adc .r9 (.mem (sc (b + 8))),
      .mov .r10 (.mem (sc (a + 16))), .alu .adc .r10 (.mem (sc (b + 16))),
      .mov .r11 (.mem (sc (a + 24))), .alu .adc .r11 (.mem (sc (b + 24))),
      .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)] ++ (carry38 ++ store4 o) from rfl,
    WP.block_append_iff]
  refine WP.mono (addPre_ok hs ha hb) fun s₁ ⟨c, hc, e1, x1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (carry38_ok s₁ (by omega_arith)) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  refine WP.mono (store4_ok hs₂ ho) fun s₃ ⟨m3, g3, rd3, wr3⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g3, k2.1 r (by simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1]), k1.1 r (by simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1])]
  · rw [rd3, k2.2.2.1, k1.2.2.1]
  · rw [wr3, k2.2.2.2, k1.2.2.2]
  · rw [m3, k2.2.1, k1.2.1]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_add
    rw [m3, fe_st4 _ _ (by omega), e2, x1, ← e1, fold256]

/-- The difference of `[a]` and `[b]` into `r8–r11`, and `38 ×` its borrow
into `rax`. -/
theorem subPre_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat} (ha : Slot a)
    (hb : Slot b) :
    WP isa (.block [.mov .r8 (.mem (sc a)), .alu .sub .r8 (.mem (sc b)),
      .mov .r9 (.mem (sc (a + 8))), .alu .sbb .r9 (.mem (sc (b + 8))),
      .mov .r10 (.mem (sc (a + 16))), .alu .sbb .r10 (.mem (sc (b + 16))),
      .mov .r11 (.mem (sc (a + 24))), .alu .sbb .r11 (.mem (sc (b + 24))),
      .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)]) s fun s' =>
      ∃ c : Nat, c ≤ 1 ∧
        val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + fe s.mem base b =
          fe s.mem base a + 2 ^ 256 * c ∧
        (s'.gpr .rax).toNat = 38 * c ∧ Keeps [.r8, .r9, .r10, .r11, .rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load64,
    ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, hs.rdi, ld_sc hs (d := a) (by omega),
    ld_sc hs (d := b) (by omega), ld_sc hs (d := a + 8) (by omega),
    ld_sc hs (d := b + 8) (by omega), ld_sc hs (d := a + 16) (by omega),
    ld_sc hs (d := b + 16) (by omega), ld_sc hs (d := a + 24) (by omega),
    ld_sc hs (d := b + 24) (by omega), ite_true, ite_false, reduceCtorEq, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨_, Bool.toNat_le _, ?_, mask38 _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  · exact chain_sub _ _ _ _ _ _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2, ite_false]

/-- `r8–r11 - rax`, and `38 ×` its borrow into `rax`. -/
theorem borrow38_ok (s : State) :
    WP isa (.block [.alu .sub .r8 (.reg .rax), .alu .sbb .r9 (.imm 0), .alu .sbb .r10 (.imm 0),
      .alu .sbb .r11 (.imm 0), .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)]) s fun s' =>
      ∃ c : Nat, c ≤ 1 ∧
        val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + (s.gpr .rax).toNat =
          val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) + 2 ^ 256 * c ∧
        (s'.gpr .rax).toNat = 38 * c ∧ Keeps [.r8, .r9, .r10, .r11, .rax] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true,
    ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', se0]
  refine ⟨_, Bool.toNat_le _, ?_, mask38 _ _, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := chain_sub (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .rax) 0 0 0
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    simp only [val4, hz, Nat.mul_zero, Nat.add_zero] at e ⊢
    exact e
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2, ite_false]

/-- `r8 - rax`, when it does not borrow. -/
theorem subLow_ok (s : State) (h : (s.gpr .rax).toNat ≤ (s.gpr .r8).toNat) :
    WP isa (.block [.alu .sub .r8 (.reg .rax)]) s fun s' =>
      (s'.gpr .r8).toNat + (s.gpr .rax).toNat = (s.gpr .r8).toNat ∧ Keeps [.r8] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [BitVec.toNat_sub]
    have := (s.gpr .r8).isLt
    rw [show 2 ^ 64 - (s.gpr .rax).toNat + (s.gpr .r8).toNat =
      (s.gpr .r8).toNat - (s.gpr .rax).toNat + 2 ^ 64 by omega_arith, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega_arith)]
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- `[o] = [a] - [b]`. -/
theorem sub_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (sub o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a - F s.mem base b := by
  rw [show sub o a b = [.mov .r8 (.mem (sc a)), .alu .sub .r8 (.mem (sc b)),
      .mov .r9 (.mem (sc (a + 8))), .alu .sbb .r9 (.mem (sc (b + 8))),
      .mov .r10 (.mem (sc (a + 16))), .alu .sbb .r10 (.mem (sc (b + 16))),
      .mov .r11 (.mem (sc (a + 24))), .alu .sbb .r11 (.mem (sc (b + 24))),
      .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)] ++
      ([.alu .sub .r8 (.reg .rax), .alu .sbb .r9 (.imm 0), .alu .sbb .r10 (.imm 0),
      .alu .sbb .r11 (.imm 0), .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)] ++
      ([.alu .sub .r8 (.reg .rax)] ++ store4 o)) from rfl, WP.block_append_iff]
  refine WP.mono (subPre_ok hs ha hb) fun s₁ ⟨c, hc, e1, x1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (borrow38_ok s₁) fun s₂ ⟨c', hc', e2, x2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  have hlow : (s₂.gpr .rax).toNat ≤ (s₂.gpr .r8).toNat := by
    rw [x2]
    rcases Nat.lt_or_ge c' 1 with h | h
    · omega_arith
    · simp only [val4] at e2
      have := (s₂.gpr .r9).isLt; have := (s₂.gpr .r10).isLt; have := (s₂.gpr .r11).isLt
      have := (s₁.gpr .r8).isLt; have := (s₁.gpr .r9).isLt; have := (s₁.gpr .r10).isLt
      have := (s₁.gpr .r11).isLt
      omega_arith
  rw [WP.block_append_iff]
  refine WP.mono (subLow_ok s₂ hlow) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  refine WP.mono (store4_ok hs₃ ho) fun s₄ ⟨m4, g4, rd4, wr4⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g4, k3.1 r (by simp [hr.2.2.2.2.1]),
      k2.1 r (by simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1]),
      k1.1 r (by simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1])]
  · rw [rd4, k3.2.2.1, k2.2.2.1, k1.2.2.1]
  · rw [wr4, k3.2.2.2, k2.2.2.2, k1.2.2.2]
  · rw [m4, k3.2.1, k2.2.1, k1.2.1]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_sub
    rw [m4, fe_st4 _ _ (by omega)]
    have r9 := k3.1 .r9 (by decide); have r10 := k3.1 .r10 (by decide)
    have r11 := k3.1 .r11 (by decide)
    simp only [val4] at e1 e2 ⊢
    rw [r9, r10, r11]
    rw [x1] at e2
    rw [x2] at e3
    simp only [VG.Spec.X25519.P]
    omega_arith

/-! ## Sums and differences with one fold

`addL` and `subL` fold the carry or borrow out once. That is enough when one
operand of a sum, or the subtrahend of a difference, is at most `2p`, as every
product is (`mulBnd_ok`): the sum is then below `2²⁵⁷ - 38`, and the
difference above `-2p`. -/

theorem val4_lt (a0 a1 a2 a3 : BitVec 64) : val4 a0 a1 a2 a3 < 2 ^ 256 := by
  simp only [val4]
  have := a0.isLt; have := a1.isLt; have := a2.isLt; have := a3.isLt
  omega_arith

theorem fe_lt4 (m : Mem) (base : Addr) (a : Nat) : fe m base a < 2 ^ 256 := val4_lt _ _ _ _

/-- `r8–r11 + rax`, and its carry out. -/
theorem carryAdd_ok (s : State) :
    WP isa (.block [.alu .add .r8 (.reg .rax), .alu .adc .r9 (.imm 0), .alu .adc .r10 (.imm 0),
      .alu .adc .r11 (.imm 0)]) s fun s' =>
      ∃ c : Nat, c ≤ 1 ∧
        val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + 2 ^ 256 * c =
          val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) + (s.gpr .rax).toNat ∧
        Keeps [.r8, .r9, .r10, .r11] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true,
    ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', se0]
  have e := chain_add (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .rax) 0 0 0
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  simp only [val4, hz, Nat.mul_zero, Nat.add_zero] at e ⊢
  refine ⟨_, Bool.toNat_le _, e, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2,
    ite_false]

/-- `r8–r11 - rax`, and its borrow out. -/
theorem borrowSub_ok (s : State) :
    WP isa (.block [.alu .sub .r8 (.reg .rax), .alu .sbb .r9 (.imm 0), .alu .sbb .r10 (.imm 0),
      .alu .sbb .r11 (.imm 0)]) s fun s' =>
      ∃ c : Nat, c ≤ 1 ∧
        val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + (s.gpr .rax).toNat =
          val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) + 2 ^ 256 * c ∧
        Keeps [.r8, .r9, .r10, .r11] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true,
    ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left', se0]
  have e := chain_sub (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (s.gpr .rax) 0 0 0
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  simp only [val4, hz, Nat.mul_zero, Nat.add_zero] at e ⊢
  refine ⟨_, Bool.toNat_le _, e, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2,
    ite_false]

/-- `A ≡ B` if they differ by a multiple of `p`. -/
theorem mod_of_add_mul {A B k : Nat} (h : A + VG.Spec.X25519.P * k = B) :
    A % VG.Spec.X25519.P = B % VG.Spec.X25519.P := by
  rw [← h, Nat.add_mul_mod_self_left]

/-- `[o] = [a] + [b]`, folded once, if `[a]` or `[b]` is at most `2p`. -/
theorem addL_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b)
    (hab : fe s.mem base a ≤ 2 * VG.Spec.X25519.P ∨ fe s.mem base b ≤ 2 * VG.Spec.X25519.P) :
    WP isa (.block (addL o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a + F s.mem base b := by
  rw [show addL o a b = [.mov .r8 (.mem (sc a)), .alu .add .r8 (.mem (sc b)),
      .mov .r9 (.mem (sc (a + 8))), .alu .adc .r9 (.mem (sc (b + 8))),
      .mov .r10 (.mem (sc (a + 16))), .alu .adc .r10 (.mem (sc (b + 16))),
      .mov .r11 (.mem (sc (a + 24))), .alu .adc .r11 (.mem (sc (b + 24))),
      .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)] ++
      (([.alu .add .r8 (.reg .rax), .alu .adc .r9 (.imm 0), .alu .adc .r10 (.imm 0),
      .alu .adc .r11 (.imm 0)] : List Instr) ++ store4 o) from rfl, WP.block_append_iff]
  refine WP.mono (addPre_ok hs ha hb) fun s₁ ⟨c, hc, e1, x1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (carryAdd_ok s₁) fun s₂ ⟨c', hc', e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  refine WP.mono (store4_ok hs₂ ho) fun s₃ ⟨m3, g3, rd3, wr3⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g3, k2.1 r (by simp [hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1]), k1.1 r (by simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1])]
  · rw [rd3, k2.2.2.1, k1.2.2.1]
  · rw [wr3, k2.2.2.2, k1.2.2.2]
  · rw [m3, k2.2.1, k1.2.1]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_add
    rw [m3, fe_st4 _ _ (by omega)]
    have la := fe_lt4 s.mem base a; have lb := fe_lt4 s.mem base b
    have l1 := fe_lt4 s₃.mem base o
    have hv : val4 (s₂.gpr .r8) (s₂.gpr .r9) (s₂.gpr .r10) (s₂.gpr .r11) < 2 ^ 256 :=
      val4_lt _ _ _ _
    have hv1 : val4 (s₁.gpr .r8) (s₁.gpr .r9) (s₁.gpr .r10) (s₁.gpr .r11) < 2 ^ 256 :=
      val4_lt _ _ _ _
    rw [x1] at e2
    generalize val4 (s₂.gpr .r8) (s₂.gpr .r9) (s₂.gpr .r10) (s₂.gpr .r11) = V at *
    generalize val4 (s₁.gpr .r8) (s₁.gpr .r9) (s₁.gpr .r10) (s₁.gpr .r11) = U at *
    refine mod_of_add_mul (k := 2 * c) ?_
    simp only [VG.Spec.X25519.P] at hab ⊢
    omega_arith

/-- `[o] = [a] - [b]`, folded once, if `[b]` is at most `2p`. -/
theorem subL_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) (hb2 : fe s.mem base b ≤ 2 * VG.Spec.X25519.P) :
    WP isa (.block (subL o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a - F s.mem base b := by
  rw [show subL o a b = [.mov .r8 (.mem (sc a)), .alu .sub .r8 (.mem (sc b)),
      .mov .r9 (.mem (sc (a + 8))), .alu .sbb .r9 (.mem (sc (b + 8))),
      .mov .r10 (.mem (sc (a + 16))), .alu .sbb .r10 (.mem (sc (b + 16))),
      .mov .r11 (.mem (sc (a + 24))), .alu .sbb .r11 (.mem (sc (b + 24))),
      .alu .sbb .rax (.reg .rax), .alu .and .rax (.imm 38)] ++
      (([.alu .sub .r8 (.reg .rax), .alu .sbb .r9 (.imm 0), .alu .sbb .r10 (.imm 0),
      .alu .sbb .r11 (.imm 0)] : List Instr) ++ store4 o) from rfl, WP.block_append_iff]
  refine WP.mono (subPre_ok hs ha hb) fun s₁ ⟨c, hc, e1, x1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (borrowSub_ok s₁) fun s₂ ⟨c', hc', e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  refine WP.mono (store4_ok hs₂ ho) fun s₃ ⟨m3, g3, rd3, wr3⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g3, k2.1 r (by simp [hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1]), k1.1 r (by simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1])]
  · rw [rd3, k2.2.2.1, k1.2.2.1]
  · rw [wr3, k2.2.2.2, k1.2.2.2]
  · rw [m3, k2.2.1, k1.2.1]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_sub
    rw [m3, fe_st4 _ _ (by omega)]
    have la := fe_lt4 s.mem base a; have lb := fe_lt4 s.mem base b
    have hv : val4 (s₂.gpr .r8) (s₂.gpr .r9) (s₂.gpr .r10) (s₂.gpr .r11) < 2 ^ 256 :=
      val4_lt _ _ _ _
    have hv1 : val4 (s₁.gpr .r8) (s₁.gpr .r9) (s₁.gpr .r10) (s₁.gpr .r11) < 2 ^ 256 :=
      val4_lt _ _ _ _
    rw [x1] at e2
    generalize val4 (s₂.gpr .r8) (s₂.gpr .r9) (s₂.gpr .r10) (s₂.gpr .r11) = V at *
    generalize val4 (s₁.gpr .r8) (s₁.gpr .r9) (s₁.gpr .r10) (s₁.gpr .r11) = U at *
    refine (mod_of_add_mul (k := 2 * c) ?_).symm
    simp only [VG.Spec.X25519.P] at hb2 ⊢
    omega_arith


/-! ## Sums and differences with one fold, selected by `cmov` -/

theorem cmov38 (c : Bool) :
    (if (!c) = true then (0 : BitVec 64) else BitVec.setWidth 64 (38 : BitVec 32)).toNat =
      38 * c.toNat := by
  cases c <;> rfl

/-- A field of the state a `cmov` leaves: of the state it writes or of the one it keeps. -/
theorem gpr_ite {p : Prop} [Decidable p] (s₁ s₂ : State) (r : Reg) :
    (if p then s₁ else s₂).gpr r = if p then s₁.gpr r else s₂.gpr r := apply_ite (State.gpr · r) p s₁ s₂

theorem mem_ite {p : Prop} [Decidable p] (s₁ s₂ : State) :
    (if p then s₁ else s₂).mem = if p then s₁.mem else s₂.mem := apply_ite State.mem p s₁ s₂

theorem rd_ite {p : Prop} [Decidable p] (s₁ s₂ : State) :
    (if p then s₁ else s₂).rd = if p then s₁.rd else s₂.rd := apply_ite State.rd p s₁ s₂

theorem wr_ite {p : Prop} [Decidable p] (s₁ s₂ : State) :
    (if p then s₁ else s₂).wr = if p then s₁.wr else s₂.wr := apply_ite State.wr p s₁ s₂

/-- `addCmov`'s start: the sum of `[a]` and `[b]` into `r8–r11`, and `38 ×` its carry into `rax`. -/
theorem addCmovPre_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat} (ha : Slot a)
    (hb : Slot b) :
    WP isa (.block [.alu32 .xor .rcx (.reg .rcx), .mov32 .rax (.imm 38),
      .mov .r8 (.mem (sc a)), .alu .add .r8 (.mem (sc b)),
      .mov .r9 (.mem (sc (a + 8))), .alu .adc .r9 (.mem (sc (b + 8))),
      .mov .r10 (.mem (sc (a + 16))), .alu .adc .r10 (.mem (sc (b + 16))),
      .mov .r11 (.mem (sc (a + 24))), .alu .adc .r11 (.mem (sc (b + 24))),
      .cmov .ae .rax (.reg .rcx)]) s fun s' =>
      ∃ c : Nat, c ≤ 1 ∧
        val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + 2 ^ 256 * c =
          fe s.mem base a + fe s.mem base b ∧
        (s'.gpr .rax).toNat = 38 * c ∧ Keeps [.r8, .r9, .r10, .r11, .rax, .rcx] s s' := by
  obtain ⟨a0, h0⟩ : ∃ v, s.mem.readW (off base a) 64 = v := ⟨_, rfl⟩
  obtain ⟨a1, h1⟩ : ∃ v, s.mem.readW (off base (a + 8)) 64 = v := ⟨_, rfl⟩
  obtain ⟨a2, h2⟩ : ∃ v, s.mem.readW (off base (a + 16)) 64 = v := ⟨_, rfl⟩
  obtain ⟨a3, h3⟩ : ∃ v, s.mem.readW (off base (a + 24)) 64 = v := ⟨_, rfl⟩
  obtain ⟨b0, h4⟩ : ∃ v, s.mem.readW (off base b) 64 = v := ⟨_, rfl⟩
  obtain ⟨b1, h5⟩ : ∃ v, s.mem.readW (off base (b + 8)) 64 = v := ⟨_, rfl⟩
  obtain ⟨b2, h6⟩ : ∃ v, s.mem.readW (off base (b + 16)) 64 = v := ⟨_, rfl⟩
  obtain ⟨b3, h7⟩ : ∃ v, s.mem.readW (off base (b + 24)) 64 = v := ⟨_, rfl⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
    execAlu32, execCmov, eval, State.load64, State.setReg32,
    ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, hs.rdi, ld_sc hs (d := a) (by omega),
    ld_sc hs (d := b) (by omega), ld_sc hs (d := a + 8) (by omega),
    ld_sc hs (d := b + 8) (by omega), ld_sc hs (d := a + 16) (by omega),
    ld_sc hs (d := b + 16) (by omega), ld_sc hs (d := a + 24) (by omega),
    ld_sc hs (d := b + 24) (by omega), ite_true, ite_false, reduceCtorEq, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.xor_self, fe, word, h0, h1, h2,
    h3, h4, h5, h6, h7, gpr_ite, ite_self]
  have e := chain_add a0 a1 a2 a3 b0 b1 b2 b3
  simp only at e
  obtain ⟨c, hc⟩ : ∃ c, decide (2 ^ 64 ≤ a3.toNat + b3.toNat + (decide (2 ^ 64 ≤ a2.toNat + b2.toNat +
      (decide (2 ^ 64 ≤ a1.toNat + b1.toNat + (decide (2 ^ 64 ≤ a0.toNat + b0.toNat)).toNat)).toNat)).toNat) = c := ⟨_, rfl⟩
  simp only [hc] at e ⊢
  refine ⟨c.toNat, Bool.toNat_le _, e, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · cases c <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_ite, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false, ite_self]
  · simp only [mem_ite, RegUpd.mem_setReg, RegUpd.mem_arithFlags, ite_self]
  · simp only [rd_ite, RegUpd.rd_setReg, RegUpd.rd_arithFlags, ite_self]
  · simp only [wr_ite, RegUpd.wr_setReg, RegUpd.wr_arithFlags, ite_self]

/-- `subCmov`'s start: the difference of `[a]` and `[b]` into `r8–r11`, and `38 ×` its borrow
into `rax`. -/
theorem subCmovPre_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat} (ha : Slot a)
    (hb : Slot b) :
    WP isa (.block [.alu32 .xor .rcx (.reg .rcx), .mov32 .rax (.imm 38),
      .mov .r8 (.mem (sc a)), .alu .sub .r8 (.mem (sc b)),
      .mov .r9 (.mem (sc (a + 8))), .alu .sbb .r9 (.mem (sc (b + 8))),
      .mov .r10 (.mem (sc (a + 16))), .alu .sbb .r10 (.mem (sc (b + 16))),
      .mov .r11 (.mem (sc (a + 24))), .alu .sbb .r11 (.mem (sc (b + 24))),
      .cmov .ae .rax (.reg .rcx)]) s fun s' =>
      ∃ c : Nat, c ≤ 1 ∧
        val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + fe s.mem base b =
          fe s.mem base a + 2 ^ 256 * c ∧
        (s'.gpr .rax).toNat = 38 * c ∧ Keeps [.r8, .r9, .r10, .r11, .rax, .rcx] s s' := by
  obtain ⟨a0, h0⟩ : ∃ v, s.mem.readW (off base a) 64 = v := ⟨_, rfl⟩
  obtain ⟨a1, h1⟩ : ∃ v, s.mem.readW (off base (a + 8)) 64 = v := ⟨_, rfl⟩
  obtain ⟨a2, h2⟩ : ∃ v, s.mem.readW (off base (a + 16)) 64 = v := ⟨_, rfl⟩
  obtain ⟨a3, h3⟩ : ∃ v, s.mem.readW (off base (a + 24)) 64 = v := ⟨_, rfl⟩
  obtain ⟨b0, h4⟩ : ∃ v, s.mem.readW (off base b) 64 = v := ⟨_, rfl⟩
  obtain ⟨b1, h5⟩ : ∃ v, s.mem.readW (off base (b + 8)) 64 = v := ⟨_, rfl⟩
  obtain ⟨b2, h6⟩ : ∃ v, s.mem.readW (off base (b + 16)) 64 = v := ⟨_, rfl⟩
  obtain ⟨b3, h7⟩ : ∃ v, s.mem.readW (off base (b + 24)) 64 = v := ⟨_, rfl⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32, execAlu,
    execAlu32, execCmov, eval, State.load64, State.setReg32,
    ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, hs.rdi, ld_sc hs (d := a) (by omega),
    ld_sc hs (d := b) (by omega), ld_sc hs (d := a + 8) (by omega),
    ld_sc hs (d := b + 8) (by omega), ld_sc hs (d := a + 16) (by omega),
    ld_sc hs (d := b + 16) (by omega), ld_sc hs (d := a + 24) (by omega),
    ld_sc hs (d := b + 24) (by omega), ite_true, ite_false, reduceCtorEq, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.xor_self, fe, word, h0, h1, h2,
    h3, h4, h5, h6, h7, gpr_ite, ite_self]
  have e := chain_sub a0 a1 a2 a3 b0 b1 b2 b3
  simp only at e
  obtain ⟨c, hc⟩ : ∃ c, decide (a3.toNat < b3.toNat + (decide (a2.toNat < b2.toNat +
      (decide (a1.toNat < b1.toNat + (decide (a0.toNat < b0.toNat)).toNat)).toNat)).toNat) = c := ⟨_, rfl⟩
  simp only [hc] at e ⊢
  refine ⟨c.toNat, Bool.toNat_le _, e, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · cases c <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [gpr_ite, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1,
      hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false, ite_self]
  · simp only [mem_ite, RegUpd.mem_setReg, RegUpd.mem_arithFlags, ite_self]
  · simp only [rd_ite, RegUpd.rd_setReg, RegUpd.rd_arithFlags, ite_self]
  · simp only [wr_ite, RegUpd.wr_setReg, RegUpd.wr_arithFlags, ite_self]


/-- `[o] = [a] + [b]`, folded once (`cmov`), if `[a]` or `[b]` is at most `2p`. -/
theorem addCmov_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b)
    (hab : fe s.mem base a ≤ 2 * VG.Spec.X25519.P ∨ fe s.mem base b ≤ 2 * VG.Spec.X25519.P) :
    WP isa (.block (addCmov o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a + F s.mem base b := by
  rw [show addCmov o a b = [.alu32 .xor .rcx (.reg .rcx), .mov32 .rax (.imm 38),
      .mov .r8 (.mem (sc a)), .alu .add .r8 (.mem (sc b)),
      .mov .r9 (.mem (sc (a + 8))), .alu .adc .r9 (.mem (sc (b + 8))),
      .mov .r10 (.mem (sc (a + 16))), .alu .adc .r10 (.mem (sc (b + 16))),
      .mov .r11 (.mem (sc (a + 24))), .alu .adc .r11 (.mem (sc (b + 24))),
      .cmov .ae .rax (.reg .rcx)] ++
      (([.alu .add .r8 (.reg .rax), .alu .adc .r9 (.imm 0), .alu .adc .r10 (.imm 0),
      .alu .adc .r11 (.imm 0)] : List Instr) ++ store4 o) from rfl, WP.block_append_iff]
  refine WP.mono (addCmovPre_ok hs ha hb) fun s₁ ⟨c, hc, e1, x1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (carryAdd_ok s₁) fun s₂ ⟨c', hc', e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  refine WP.mono (store4_ok hs₂ ho) fun s₃ ⟨m3, g3, rd3, wr3⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g3, k2.1 r (by simp [hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1]), k1.1 r (by simp [hr.1, hr.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1])]
  · rw [rd3, k2.2.2.1, k1.2.2.1]
  · rw [wr3, k2.2.2.2, k1.2.2.2]
  · rw [m3, k2.2.1, k1.2.1]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_add
    rw [m3, fe_st4 _ _ (by omega)]
    have la := fe_lt4 s.mem base a; have lb := fe_lt4 s.mem base b
    have hv : val4 (s₂.gpr .r8) (s₂.gpr .r9) (s₂.gpr .r10) (s₂.gpr .r11) < 2 ^ 256 :=
      val4_lt _ _ _ _
    have hv1 : val4 (s₁.gpr .r8) (s₁.gpr .r9) (s₁.gpr .r10) (s₁.gpr .r11) < 2 ^ 256 :=
      val4_lt _ _ _ _
    rw [x1] at e2
    generalize val4 (s₂.gpr .r8) (s₂.gpr .r9) (s₂.gpr .r10) (s₂.gpr .r11) = V at *
    generalize val4 (s₁.gpr .r8) (s₁.gpr .r9) (s₁.gpr .r10) (s₁.gpr .r11) = U at *
    refine mod_of_add_mul (k := 2 * c) ?_
    simp only [VG.Spec.X25519.P] at hab ⊢
    omega_arith

/-- `[o] = [a] - [b]`, folded once (`cmov`), if `[b]` is at most `2p`. -/
theorem subCmov_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b)
    (hb2 : fe s.mem base b ≤ 2 * VG.Spec.X25519.P) :
    WP isa (.block (subCmov o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a - F s.mem base b := by
  rw [show subCmov o a b = [.alu32 .xor .rcx (.reg .rcx), .mov32 .rax (.imm 38),
      .mov .r8 (.mem (sc a)), .alu .sub .r8 (.mem (sc b)),
      .mov .r9 (.mem (sc (a + 8))), .alu .sbb .r9 (.mem (sc (b + 8))),
      .mov .r10 (.mem (sc (a + 16))), .alu .sbb .r10 (.mem (sc (b + 16))),
      .mov .r11 (.mem (sc (a + 24))), .alu .sbb .r11 (.mem (sc (b + 24))),
      .cmov .ae .rax (.reg .rcx)] ++
      (([.alu .sub .r8 (.reg .rax), .alu .sbb .r9 (.imm 0), .alu .sbb .r10 (.imm 0),
      .alu .sbb .r11 (.imm 0)] : List Instr) ++ store4 o) from rfl, WP.block_append_iff]
  refine WP.mono (subCmovPre_ok hs ha hb) fun s₁ ⟨c, hc, e1, x1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (borrowSub_ok s₁) fun s₂ ⟨c', hc', e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  refine WP.mono (store4_ok hs₂ ho) fun s₃ ⟨m3, g3, rd3, wr3⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g3, k2.1 r (by simp [hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1]), k1.1 r (by simp [hr.1, hr.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1])]
  · rw [rd3, k2.2.2.1, k1.2.2.1]
  · rw [wr3, k2.2.2.2, k1.2.2.2]
  · rw [m3, k2.2.1, k1.2.1]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_sub
    rw [m3, fe_st4 _ _ (by omega)]
    have la := fe_lt4 s.mem base a; have lb := fe_lt4 s.mem base b
    have hv : val4 (s₂.gpr .r8) (s₂.gpr .r9) (s₂.gpr .r10) (s₂.gpr .r11) < 2 ^ 256 :=
      val4_lt _ _ _ _
    have hv1 : val4 (s₁.gpr .r8) (s₁.gpr .r9) (s₁.gpr .r10) (s₁.gpr .r11) < 2 ^ 256 :=
      val4_lt _ _ _ _
    rw [x1] at e2
    generalize val4 (s₂.gpr .r8) (s₂.gpr .r9) (s₂.gpr .r10) (s₂.gpr .r11) = V at *
    generalize val4 (s₁.gpr .r8) (s₁.gpr .r9) (s₁.gpr .r10) (s₁.gpr .r11) = U at *
    refine (mod_of_add_mul (k := 2 * c) ?_).symm
    simp only [VG.Spec.X25519.P] at hb2 ⊢
    omega_arith

end VG.Proof.X25519.X86_64
