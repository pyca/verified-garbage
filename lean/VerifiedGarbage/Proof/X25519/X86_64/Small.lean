module
public import VerifiedGarbage.Proof.X25519.X86_64.Ops

import VerifiedGarbage.Proof.X25519.X86_64.AddSub
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# X25519 on x86-64: multiplication by `a24`, and the swap
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-- `[b]` into `r8–r11`. -/
theorem loadFe_ok {s : State} {base : Addr} (hs : Scr s base) {b : Nat} (hb : Slot b) :
    WP isa (.block (loads b .r8 .r9 .r10 .r11)) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) = fe s.mem base b ∧
      Keeps [.r8, .r9, .r10, .r11] s s' := by
  apply WP.of_runBlock
  simp only [loads, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_sc,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, hs.rdi,
    ld_sc hs (d := b) (by omega), ld_sc hs (d := b + 8) (by omega),
    ld_sc hs (d := b + 16) (by omega), ld_sc hs (d := b + 24) (by omega), ite_true, ite_false,
    reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- `mov ecx, k`. -/
theorem movRcxImm_ok (s : State) (k : BitVec 32) :
    WP isa (.block [.mov32 .rcx (.imm k)]) s fun s' =>
      (s'.gpr .rcx).toNat = k.toNat ∧ Keeps [.rcx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, (by trivial), (by trivial), (by trivial)⟩
  · rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le k.isLt (by decide))]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr]

/-- `[b]` added to the five words `r8–r12`. -/
theorem addB_ok {s : State} {base : Addr} (hs : Scr s base) {b : Nat} (hb : Slot b)
    (h12 : (s.gpr .r12).toNat + 1 < 2 ^ 64) :
    WP isa (.block [.alu .add .r8 (.mem (sc b)), .alu .adc .r9 (.mem (sc (b + 8))),
      .alu .adc .r10 (.mem (sc (b + 16))), .alu .adc .r11 (.mem (sc (b + 24))),
      .alu .adc .r12 (.imm 0)]) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + 2 ^ 256 * (s'.gpr .r12).toNat =
        val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) + fe s.mem base b +
          2 ^ 256 * (s.gpr .r12).toNat ∧
      Keeps [.r8, .r9, .r10, .r11, .r12] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load64,
    ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.mem_arithFlags, hs.rdi, ld_sc hs (d := b) (by omega),
    ld_sc hs (d := b + 8) (by omega), ld_sc hs (d := b + 16) (by omega),
    ld_sc hs (d := b + 24) (by omega), ite_true, ite_false, reduceCtorEq, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left', se0]
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have e := chain_add (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) (word s.mem base b)
      (word s.mem base (b + 8)) (word s.mem base (b + 16)) (word s.mem base (b + 24))
    simp only at e
    generalize decide (2 ^ 64 ≤ (s.gpr .r11).toNat + _ + _) = c3 at e ⊢
    have e4 := adc_carry (s.gpr .r12) 0 c3
    have hc := Bool.toNat_le c3
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    rw [hz, Nat.add_zero, show decide (2 ^ 64 ≤ (s.gpr .r12).toNat + c3.toNat) = false from
      decide_eq_false (by omega_arith), Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at e4
    simp only [X86_64.fe, val4, word] at e ⊢
    omega_using [e, e4]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2, ite_false]

/-- `[o] = [b] + a24 · [a]`. -/
theorem mulA24Add_ok {s : State} {base : Addr} (hs : Scr s base) {o b a : Nat} (ho : Slot o)
    (hb : Slot b) (ha : Slot a) :
    WP isa (.block (mulSmallAdd o b a a24)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base b + Spec.X25519.a24 * F s.mem base a := by
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  simp only [mulSmallAdd, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (movRcxImm_ok s a24) fun s₁ ⟨c1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (prod2_ok s₁ (b := .rcx) (readSrc_sc hs₁ (by omega)) (by decide) (by decide))
    fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s₂ .r10) fun s₃ ⟨z3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s₃ .r11) fun s₄ ⟨z4, k4⟩ => ?_
  have hs₄ := hs₃.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s₄ .r12) fun s₅ ⟨z5, k5⟩ => ?_
  have hs₅ := hs₄.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (acc2_ok s₅ (b := .rcx) (readSrc_sc hs₅ (by omega)) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₆ ⟨⟨c6, e6⟩, k6⟩ => ?_
  have hs₆ := hs₅.of_keeps k6 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (acc2_ok s₆ (b := .rcx) (readSrc_sc hs₆ (by omega)) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₇ ⟨⟨c7, e7⟩, k7⟩ => ?_
  have hs₇ := hs₆.of_keeps k7 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (acc2_ok s₇ (b := .rcx) (readSrc_sc hs₇ (by omega)) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₈ ⟨⟨c8, e8⟩, k8⟩ => ?_
  have hs₈ := hs₇.of_keeps k8 (by decide)
  -- The words of `a24 · [a]`: no carry is lost.
  simp only [reduceCtorEq, ite_false] at e2
  simp (disch := decide) only [k2.1, k3.1, k4.1, k5.1, k6.1, k7.1, k1.2.1, k2.2.1, k3.2.1,
    k4.2.1, k5.2.1, k6.2.1, k7.2.1, z3, z4, z5, hz, Nat.mul_zero, Nat.add_zero, c1,
    show a24.toNat = 121665 from rfl] at e2 e6 e7 e8
  have w0 := (word s.mem base a).isLt; have w1 := (word s.mem base (a + 8)).isLt
  have w2 := (word s.mem base (a + 16)).isLt; have w3 := (word s.mem base (a + 24)).isLt
  have l9 := (s₂.gpr .r9).isLt; have l10 := (s₆.gpr .r10).isLt; have l11 := (s₇.gpr .r11).isLt
  have h6 := Bool.toNat_le c6; have h7 := Bool.toNat_le c7; have h8 := Bool.toNat_le c8
  have z6 : c6.toNat = 0 := by omega_using [e6, h6, l9, w1]
  have z7 : c7.toNat = 0 := by omega_using [e7, h7, l10, w2]
  have z8 : c8.toNat = 0 := by omega_using [e8, h8, l11, w3]
  rw [z6, Nat.mul_zero, Nat.add_zero] at e6
  rw [z7, Nat.mul_zero, Nat.add_zero] at e7
  rw [z8, Nat.mul_zero, Nat.add_zero] at e8
  have h12 : (s₈.gpr .r12).toNat < 2 ^ 32 := by omega_using [e8, l11, w3]
  rw [WP.block_append_iff]
  refine WP.mono (addB_ok hs₈ hb (by omega_using [h12])) fun s₉ ⟨e9, k9⟩ => ?_
  have hs₉ := hs₈.of_keeps k9 (by decide)
  have h12' : (s₉.gpr .r12).toNat < 2 ^ 56 := by
    have v8 := val4_lt (s₈.gpr .r8) (s₈.gpr .r9) (s₈.gpr .r10) (s₈.gpr .r11)
    have vb := fe_lt4 s₈.mem base b
    omega_using [e9, h12, v8, vb]
  rw [WP.block_append_iff]
  refine WP.mono (fold19X_ok s₉ h12') fun s₁₀ ⟨e10, _, k10⟩ => ?_
  have hs₁₀ := hs₉.of_keeps k10 (by decide)
  refine WP.mono (store4_ok hs₁₀ ho) fun s₁₁ ⟨m11, g11, rd11, wr11⟩ => ?_
  have K : Keeps clob s s₁₀ :=
    (k1.mono (by decide)).trans ((k2.mono (by decide)).trans ((k3.mono (by decide)).trans
    ((k4.mono (by decide)).trans ((k5.mono (by decide)).trans ((k6.mono (by decide)).trans
    ((k7.mono (by decide)).trans ((k8.mono (by decide)).trans ((k9.mono (by decide)).trans
    (k10.mono (by decide))))))))))
  refine ⟨⟨fun r hr => (g11 r).trans (K.1 r hr), rd11.trans K.2.2.1, wr11.trans K.2.2.2, ?_⟩, ?_⟩
  · rw [m11, K.2.1]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_addA24
    rw [m11, fe_st4 _ _ (by omega), e10]
    congr 1
    simp (disch := decide) only [k3.1, k4.1, k5.1, k6.1, k7.1, k8.1, k1.2.1, k2.2.1,
      k3.2.1, k4.2.1, k5.2.1, k6.2.1, k7.2.1, k8.2.1] at e9
    simp only [X86_64.fe, val4] at e9 ⊢
    omega_using [e2, e6, e7, e8, e9]

/-! ## The conditional swap -/

/-- The mask of a swap bit: all ones for a swap, zero otherwise. -/
def mask (sw : Bool) : BitVec 64 := if sw then BitVec.allOnes 64 else 0

theorem xor_sel (sw : Bool) (a b : BitVec 64) :
    a ^^^ ((a ^^^ b) &&& mask sw) = (if sw then b else a) ∧
      b ^^^ ((a ^^^ b) &&& mask sw) = (if sw then a else b) := by
  cases sw
  · simp only [mask, Bool.false_eq_true, ite_false]
    constructor <;> (apply BitVec.eq_of_toNat_eq; simp)
  · simp only [mask, ite_true, BitVec.and_allOnes]
    constructor
    · rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · rw [BitVec.xor_comm a b, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem cswap_eq (x y : Nat) : cswap x y =
    (loads x .r8 .r9 .r10 .r11 ++ loads y .r12 .r13 .r14 .r15 ++
      ([.mov .rax (.reg .r8), .alu .xor .rax (.reg .r12), .alu .and .rax (.reg .rcx),
        .alu .xor .r8 (.reg .rax), .alu .xor .r12 (.reg .rax),
        .mov .rax (.reg .r9), .alu .xor .rax (.reg .r13), .alu .and .rax (.reg .rcx),
        .alu .xor .r9 (.reg .rax), .alu .xor .r13 (.reg .rax),
        .mov .rax (.reg .r10), .alu .xor .rax (.reg .r14), .alu .and .rax (.reg .rcx),
        .alu .xor .r10 (.reg .rax), .alu .xor .r14 (.reg .rax),
        .mov .rax (.reg .r11), .alu .xor .rax (.reg .r15), .alu .and .rax (.reg .rcx),
        .alu .xor .r11 (.reg .rax), .alu .xor .r15 (.reg .rax)] : List Instr)) ++
      (store4 x ++ stores y .r12 .r13 .r14 .r15) := by
  simp only [cswap, List.append_assoc]
  rfl

theorem cswapPre_ok {s : State} {base : Addr} (hs : Scr s base) {x y : Nat} (hx : Slot x)
    (hy : Slot y) {sw : Bool} (hm : s.gpr .rcx = mask sw) :
    WP isa (.block (loads x .r8 .r9 .r10 .r11 ++ loads y .r12 .r13 .r14 .r15 ++
      ([.mov .rax (.reg .r8), .alu .xor .rax (.reg .r12), .alu .and .rax (.reg .rcx),
        .alu .xor .r8 (.reg .rax), .alu .xor .r12 (.reg .rax),
        .mov .rax (.reg .r9), .alu .xor .rax (.reg .r13), .alu .and .rax (.reg .rcx),
        .alu .xor .r9 (.reg .rax), .alu .xor .r13 (.reg .rax),
        .mov .rax (.reg .r10), .alu .xor .rax (.reg .r14), .alu .and .rax (.reg .rcx),
        .alu .xor .r10 (.reg .rax), .alu .xor .r14 (.reg .rax),
        .mov .rax (.reg .r11), .alu .xor .rax (.reg .r15), .alu .and .rax (.reg .rcx),
        .alu .xor .r11 (.reg .rax), .alu .xor .r15 (.reg .rax)] : List Instr))) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) =
        (if sw then fe s.mem base y else fe s.mem base x) ∧
      val4 (s'.gpr .r12) (s'.gpr .r13) (s'.gpr .r14) (s'.gpr .r15) =
        (if sw then fe s.mem base x else fe s.mem base y) ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15, .rax] s s' := by
  apply WP.of_runBlock
  simp only [loads, List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, execAlu, State.load64, ea_sc, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, hs.rdi, hm, ld_sc hs (d := x) (by omega),
    ld_sc hs (d := y) (by omega), ld_sc hs (d := x + 8) (by omega),
    ld_sc hs (d := y + 8) (by omega), ld_sc hs (d := x + 16) (by omega),
    ld_sc hs (d := y + 16) (by omega), ld_sc hs (d := x + 24) (by omega),
    ld_sc hs (d := y + 24) (by omega), ite_true, ite_false, reduceCtorEq, Option.map_some,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  simp only [(xor_sel sw _ _).1, (xor_sel sw _ _).2]
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · cases sw <;> rfl
  · cases sw <;> rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2,
      ite_false]

/-- `[x], [y] = [y], [x]` if `sw` (the mask `rcx`), else unchanged. -/
theorem cswap_ok {s : State} {base : Addr} (hs : Scr s base) {x y : Nat} (hx : Slot x)
    (hy : Slot y) (hxy : x + 32 ≤ y ∨ y + 32 ≤ x) {sw : Bool} (hm : s.gpr .rcx = mask sw) :
    WP isa (.block (cswap x y)) s fun s' =>
      (∀ r, r ∉ clob → s'.gpr r = s.gpr r) ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ (∃ m₁, Outside base x 32 s.mem m₁ ∧ Outside base y 32 m₁ s'.mem ∧
        fe m₁ base x = (if sw then fe s.mem base y else fe s.mem base x)) ∧
      fe s'.mem base x = (if sw then fe s.mem base y else fe s.mem base x) ∧
      fe s'.mem base y = (if sw then fe s.mem base x else fe s.mem base y) := by
  rw [cswap_eq, WP.block_append_iff]
  refine WP.mono (cswapPre_ok hs hx hy hm) fun s₁ ⟨e1, e2, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (store4_ok hs₁ hx) fun s₂ ⟨m2, g2, rd2, wr2⟩ => ?_
  have hs₂ : Scr s₂ base := ⟨(g2 _).trans hs₁.rdi, wr2 ▸ hs₁.wr, hs.nowrap⟩
  refine WP.mono (stores_ok hs₂ hy _ _ _ _) fun s₃ ⟨m3, g3, rd3, wr3⟩ => ?_
  have o2 := st4_outside s₁.mem base (o := x) (by omega) (s₁.gpr .r8) (s₁.gpr .r9) (s₁.gpr .r10)
    (s₁.gpr .r11)
  have o3 := st4_outside s₂.mem base (o := y) (by omega) (s₂.gpr .r12) (s₂.gpr .r13) (s₂.gpr .r14)
    (s₂.gpr .r15)
  rw [← m2] at o2
  rw [← m3] at o3
  have hm1 : s₁.mem = s.mem := k1.2.1
  have fx : fe s₂.mem base x = (if sw then fe s.mem base y else fe s.mem base x) := by
    rw [m2, fe_st4 _ _ (by omega), e1]
  refine ⟨fun r hr => ?_, by rw [g3, g2, k1.1 .rcx (by decide)], ?_, ?_, ⟨s₂.mem, hm1 ▸ o2, o3, fx⟩,
    ?_, ?_⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g3, g2, k1.1 r (by simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2.2.2])]
  · rw [rd3, rd2, k1.2.2.1]
  · rw [wr3, wr2, k1.2.2.2]
  · rw [o3.fe hxy (by omega), fx]
  · rw [m3, fe_st4 _ _ (by omega), g2, g2, g2, g2, e2]

/-! ## The multiplexer -/

/-- `store4`, which also keeps the flags. -/
theorem store4Z_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : Slot o) :
    WP isa (.block (store4 o)) s fun s' =>
      s'.mem = st4 s.mem base o (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) ∧
      (∀ r, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf := by
  have w : ∀ d, d + 8 ≤ 4096 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hs.wr, contains_sc hd⟩
  apply WP.of_runBlock
  simp only [store4, stores, runBlock_cons, runStep_some, runBlock_nil, exec, ea_sc, hs.rdi,
    State.store64, w o (by omega), w (o + 8) (by omega), w (o + 16) (by omega),
    w (o + 24) (by omega), ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨rfl, fun _ => trivial, trivial, trivial, trivial⟩

/-- The instructions of `mux` before its stores. -/
abbrev muxSel : List Instr :=
  [.cmov .e .r8 (.reg .r12), .cmov .e .r9 (.reg .r13), .cmov .e .r10 (.reg .r14),
    .cmov .e .r11 (.reg .r15)]

theorem mux_eq (o x y : Nat) : mux o x y =
    (loads x .r8 .r9 .r10 .r11 ++ loads y .r12 .r13 .r14 .r15 ++ muxSel) ++ store4 o := by
  simp only [mux, List.append_assoc]

/-- `[y]` into `r8–r11` if ZF is set, else `[x]`. -/
theorem muxPre_ok {s : State} {base : Addr} (hs : Scr s base) {x y : Nat} (hx : Slot x)
    (hy : Slot y) {zf : Bool} (hz : s.zf = some zf) :
    WP isa (.block (loads x .r8 .r9 .r10 .r11 ++ loads y .r12 .r13 .r14 .r15 ++ muxSel)) s
      fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) =
        (if zf then fe s.mem base y else fe s.mem base x) ∧ s'.zf = s.zf ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] s s' := by
  cases zf <;>
  · apply WP.of_runBlock
    simp only [loads, muxSel, List.cons_append, List.nil_append, runBlock_cons, runStep_some,
      runBlock_nil, exec, readSrc, execCmov, eval, State.load64, ea_sc, RegUpd.gpr_setReg,
      RegUpd.zf_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, hs.rdi, hz,
      ld_sc hs (d := x) (by omega), ld_sc hs (d := y) (by omega),
      ld_sc hs (d := x + 8) (by omega), ld_sc hs (d := y + 8) (by omega),
      ld_sc hs (d := x + 16) (by omega), ld_sc hs (d := y + 16) (by omega),
      ld_sc hs (d := x + 24) (by omega), ld_sc hs (d := y + 24) (by omega), ite_true,
      ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
      exists_eq_left', Bool.false_eq_true]
    refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
      hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2, ite_false]

/-- `[o] = [y]` if ZF is set, else `[x]`, keeping the flags. -/
theorem mux_ok {s : State} {base : Addr} (hs : Scr s base) {o x y : Nat} (ho : Slot o)
    (hx : Slot x) (hy : Slot y) {zf : Bool} (hz : s.zf = some zf) :
    WP isa (.block (mux o x y)) s fun s' =>
      Op base o s s' ∧ fe s'.mem base o = (if zf then fe s.mem base y else fe s.mem base x) ∧
        s'.zf = s.zf := by
  rw [mux_eq, WP.block_append_iff]
  refine WP.mono (muxPre_ok hs hx hy hz) fun s₁ ⟨e1, z1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  refine WP.mono (store4Z_ok hs₁ ho) fun s₂ ⟨m2, g2, rd2, wr2, z2⟩ => ?_
  have o2 := st4_outside s₁.mem base (o := o) (by omega) (s₁.gpr .r8) (s₁.gpr .r9)
    (s₁.gpr .r10) (s₁.gpr .r11)
  rw [← m2, k1.2.1] at o2
  refine ⟨⟨fun r hr => ?_, by rw [rd2, k1.2.2.1], by rw [wr2, k1.2.2.2], o2⟩, ?_, by rw [z2, z1]⟩
  · simp only [clob, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g2, k1.1 r (by simp [hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.2.2.2.2.2])]
  · rw [m2, fe_st4 _ _ (by omega), e1]

end VG.Proof.X25519.X86_64
