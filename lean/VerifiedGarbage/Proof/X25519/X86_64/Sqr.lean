module

public import VerifiedGarbage.Proof.X25519.X86_64.Ops
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.PlainSimp

/-!
# X25519 on x86-64: squaring

`sqr o a` in parts: the products `a_i a_j` (`i < j`) as columns of `mul`
(`sqrCross`), doubled (`sqrDbl`), the squares added (`sqrDiag`), and reduced
as in `mul`.
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

theorem fe_lt (m : Mem) (base : Addr) (a : Nat) : fe m base a < 2 ^ 256 := by
  simp only [X86_64.fe, val4]
  have := (word m base a).isLt; have := (word m base (a + 8)).isLt
  have := (word m base (a + 16)).isLt; have := (word m base (a + 24)).isLt
  omega_arith

/-- `a₁, a₂, a₃` into `rcx, rbp, r15`. -/
theorem sqrLoad_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : Slot a) :
    WP isa (.block [.mov .rcx (.mem (sc (a + 8))), .mov .rbp (.mem (sc (a + 16))),
      .mov .r15 (.mem (sc (a + 24)))]) s fun s' =>
      s'.gpr .rcx = word s.mem base (a + 8) ∧ s'.gpr .rbp = word s.mem base (a + 16) ∧
      s'.gpr .r15 = word s.mem base (a + 24) ∧ Keeps [.rcx, .rbp, .r15] s s' := by
  have L : ∀ e, e + 8 ≤ 4096 → InRegions (s.rd ++ s.wr) (off base e) 8 :=
    fun e he => ⟨_, List.mem_append_right _ hs.wr, contains_sc he⟩
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_sc,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, hs.rdi,
    L (a + 8) (by omega), L (a + 16) (by omega), L (a + 24) (by omega), ite_true,
    ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2, ite_false]

/-- `r9–r15 = 2 · r9–r14`. -/
theorem sqrDbl_ok (s : State) :
    WP isa (.block sqrDbl) s fun s' =>
      (s'.gpr .r9).toNat + 2 ^ 64 * (s'.gpr .r10).toNat + 2 ^ 128 * (s'.gpr .r11).toNat +
          2 ^ 192 * (s'.gpr .r12).toNat + 2 ^ 256 * (s'.gpr .r13).toNat +
          2 ^ 256 * (2 ^ 64 * (s'.gpr .r14).toNat) + 2 ^ 256 * (2 ^ 128 * (s'.gpr .r15).toNat) =
        2 * ((s.gpr .r9).toNat + 2 ^ 64 * (s.gpr .r10).toNat + 2 ^ 128 * (s.gpr .r11).toNat +
          2 ^ 192 * (s.gpr .r12).toNat + 2 ^ 256 * (s.gpr .r13).toNat +
          2 ^ 256 * (2 ^ 64 * (s.gpr .r14).toNat)) ∧
      Keeps [.r9, .r10, .r11, .r12, .r13, .r14, .r15] s s' := by
  apply WP.of_runBlock
  simp only [sqrDbl, zero, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    execAlu, execAlu32, Option.map_some, Option.bind_some, State.setReg32, RegUpd.gpr_setReg,
    RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ite_false,
    reduceCtorEq, Option.some.injEq, exists_eq_left', BitVec.xor_self]
  refine ⟨?_, fun r hr => ?_, by trivial, by trivial, by trivial⟩
  · have e9 := add_carry (s.gpr .r9) (s.gpr .r9)
    have e10 := adc_carry (s.gpr .r10) (s.gpr .r10) (decide (2 ^ 64 ≤ (s.gpr .r9).toNat +
      (s.gpr .r9).toNat))
    have e11 := adc_carry (s.gpr .r11) (s.gpr .r11) (decide (2 ^ 64 ≤ (s.gpr .r10).toNat +
      (s.gpr .r10).toNat + (decide (2 ^ 64 ≤ (s.gpr .r9).toNat + (s.gpr .r9).toNat)).toNat))
    generalize (decide (2 ^ 64 ≤ (s.gpr .r11).toNat + (s.gpr .r11).toNat +
      (decide (2 ^ 64 ≤ (s.gpr .r10).toNat + (s.gpr .r10).toNat +
        (decide (2 ^ 64 ≤ (s.gpr .r9).toNat + (s.gpr .r9).toNat)).toNat)).toNat)) = c11 at e11 ⊢
    have e12 := adc_carry (s.gpr .r12) (s.gpr .r12) c11
    generalize (decide (2 ^ 64 ≤ (s.gpr .r12).toNat + (s.gpr .r12).toNat + c11.toNat)) = c12
      at e12 ⊢
    have e13 := adc_carry (s.gpr .r13) (s.gpr .r13) c12
    generalize (decide (2 ^ 64 ≤ (s.gpr .r13).toNat + (s.gpr .r13).toNat + c12.toNat)) = c13
      at e13 ⊢
    have e14 := adc_carry (s.gpr .r14) (s.gpr .r14) c13
    generalize (decide (2 ^ 64 ≤ (s.gpr .r14).toNat + (s.gpr .r14).toNat + c13.toNat)) = c14
      at e14 ⊢
    have e15 := adc_carry (BitVec.setWidth 64 0#32) (BitVec.setWidth 64 0#32)
      c14
    have hz : (BitVec.setWidth 64 0#32).toNat = 0 := rfl
    rw [hz] at e15
    have := Bool.toNat_le c14
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]

/-- A carry's mask doubled (`add x, x`): the carry again. -/
theorem mask_cf (c : Bool) :
    decide (2 ^ 64 ≤ (0#64 - (BitVec.ofBool c).setWidth 64).toNat +
      (0#64 - (BitVec.ofBool c).setWidth 64).toNat) = c := by
  cases c <;> decide

/-- The square of the word at `d` added at `t0, t1`, with the carry that the mask `rcx` holds,
and the carry out. -/
theorem diagAdd_ok (s : State) {t0 t1 : Reg} {d : Nat} {v : BitVec 64} {c : Bool}
    (hsrc : readSrc s (.mem (sc d)) = some v)
    (hd : ([t0, t1, .rax, .rdx, .rcx] : List Reg).Nodup)
    (hm : s.gpr .rcx = 0#64 - (BitVec.ofBool c).setWidth 64) :
    WP isa (.block (diagAdd t0 t1 d)) s fun s' =>
      (∃ c' : Bool, ((s'.gpr t0).toNat + 2 ^ 64 * (s'.gpr t1).toNat + 2 ^ 128 * c'.toNat =
          (s.gpr t0).toNat + 2 ^ 64 * (s.gpr t1).toNat + v.toNat * v.toNat + c.toNat) ∧
        s'.cf = some c') ∧
      Keeps [t0, t1, .rax, .rdx, .rcx] s s' := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h0a, h0d, h0c⟩, ⟨h1a, h1d, h1c⟩, -⟩ := hd
  apply WP.of_runBlock
  simp only [diagAdd, runBlock_cons, reduceExec, hsrc, Option.map_some, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc, execMul, execAlu,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, h01, Ne.symm h01,
    h0a, h0d, h0c, h1a, h1d, h1c, Ne.symm h0d, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left', hm, mask_cf]
  obtain ⟨hmul, -⟩ := mul_lo_hi v v
  have e0 := adc_carry (s.gpr t0) (BitVec.ofNat 64 (v.toNat * v.toNat)) c
  generalize decide (2 ^ 64 ≤ (s.gpr t0).toNat + _ + c.toNat) = c0 at e0 ⊢
  have e1 := adc_carry (s.gpr t1) (BitVec.ofNat 64 (v.toNat * v.toNat / 2 ^ 64)) c0
  generalize decide (2 ^ 64 ≤ (s.gpr t1).toNat + _ + c0.toNat) = c1 at e1 ⊢
  refine ⟨⟨c1, by omega_using [hmul, e0, e1], rfl⟩, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1,
    hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- `sbb rcx, rcx`: the carry as a mask. -/
theorem sbbMask_ok (s : State) {c : Bool} (hc : s.cf = some c) :
    WP isa (.block [.alu .sbb .rcx (.reg .rcx)]) s fun s' =>
      s'.gpr .rcx = 0#64 - (BitVec.ofBool c).setWidth 64 ∧ Keeps [.rcx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc, execAlu, hc,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, ite_true,
    Option.some.injEq, exists_eq_left', BitVec.sub_self]
  refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

/-- The start of `sqrDiag`: `a₁²` and the high half of `a₀²` (in `rbp`) added at `r9–r11`. -/
theorem diag1_ok (s : State) {d : Nat} {v : BitVec 64}
    (hsrc : readSrc s (.mem (sc d)) = some v) :
    WP isa (.block [.mov .rax (.mem (sc d)), .mul .rax, .alu .add .r9 (.reg .rbp),
      .alu .adc .r10 (.reg .rax), .alu .adc .r11 (.reg .rdx)]) s fun s' =>
      (∃ c' : Bool, ((s'.gpr .r9).toNat + 2 ^ 64 * (s'.gpr .r10).toNat +
            2 ^ 128 * (s'.gpr .r11).toNat + 2 ^ 192 * c'.toNat =
          (s.gpr .r9).toNat + 2 ^ 64 * (s.gpr .r10).toNat + 2 ^ 128 * (s.gpr .r11).toNat +
            (s.gpr .rbp).toNat + 2 ^ 64 * (v.toNat * v.toNat)) ∧
        s'.cf = some c') ∧
      Keeps [.r9, .r10, .r11, .rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, reduceExec, hsrc, Option.map_some, runStep_some]
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc, execMul, execAlu,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ite_false,
    reduceCtorEq, Option.some.injEq, exists_eq_left']
  obtain ⟨hmul, -⟩ := mul_lo_hi v v
  have e0 := add_carry (s.gpr .r9) (s.gpr .rbp)
  generalize decide (2 ^ 64 ≤ (s.gpr .r9).toNat + (s.gpr .rbp).toNat) = c0 at e0 ⊢
  have e1 := adc_carry (s.gpr .r10) (BitVec.ofNat 64 (v.toNat * v.toNat)) c0
  generalize decide (2 ^ 64 ≤ (s.gpr .r10).toNat + _ + c0.toNat) = c1 at e1 ⊢
  have e2 := adc_carry (s.gpr .r11) (BitVec.ofNat 64 (v.toNat * v.toNat / 2 ^ 64)) c1
  generalize decide (2 ^ 64 ≤ (s.gpr .r11).toNat + _ + c1.toNat) = c2 at e2 ⊢
  refine ⟨⟨c2, by omega_using [hmul, e0, e1, e2], rfl⟩, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1,
    hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- `sqrProd`: the eight words of the square. -/
theorem sqrProd_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat} (ha : Slot a) :
    WP isa (.block (sqrProd a)) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) +
          2 ^ 256 * val4 (s'.gpr .r12) (s'.gpr .r13) (s'.gpr .r14) (s'.gpr .r15) =
        fe s.mem base a * fe s.mem base a ∧ Keeps clob s s' := by
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  simp only [sqrProd, sqrCross, sqrDiag, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (sqrLoad_ok hs ha) fun s₁ ⟨a1, a2, a3, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (prod2_ok s₁ (b := .rcx) (readSrc_sc hs₁ (by omega)) (by decide) (by decide))
    fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s₂ .r11) fun s₃ ⟨z3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s₃ .r12) fun s₄ ⟨z4, k4⟩ => ?_
  have hs₄ := hs₃.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s₄ .r13) fun s₅ ⟨z5, k5⟩ => ?_
  have hs₅ := hs₄.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (acc2_ok s₅ (b := .rbp) (readSrc_sc hs₅ (by omega)) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₆ ⟨⟨c6, e6⟩, k6⟩ => ?_
  have hs₆ := hs₅.of_keeps k6 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (accCol_ok (by decide) (by decide) _ s₆ hs₆
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        and_intros <;> first | decide | omega)
    (by rw [k6.1 .r13 (by decide), z5]; simp only [List.length_cons, List.length_nil]; decide))
    fun s₇ ⟨e7, _, k7⟩ => ?_
  have hs₇ := hs₆.of_keeps k7 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s₇ .r14) fun s₈ ⟨z8, k8⟩ => ?_
  have hs₈ := hs₇.of_keeps k8 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (accCol_ok (by decide) (by decide) _ s₈ hs₈
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
        and_intros <;> first | decide | omega)
    (by rw [z8]; simp only [List.length_cons, List.length_nil]; decide))
    fun s₉ ⟨e9, _, k9⟩ => ?_
  have hs₉ := hs₈.of_keeps k9 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (acc2_ok s₉ (b := .r15) (readSrc_sc hs₉ (by omega)) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₁₀ ⟨⟨c10, e10⟩, k10⟩ => ?_
  have hs₁₀ := hs₉.of_keeps k10 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sqrDbl_ok s₁₀) fun s₁₁ ⟨e11, k11⟩ => ?_
  have hs₁₁ := hs₁₀.of_keeps k11 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (prod2_ok s₁₁ (b := .rax) (readSrc_sc hs₁₁ (by omega)) (by decide) (by decide))
    fun s₁₂ ⟨e12, k12⟩ => ?_
  have hs₁₂ := hs₁₁.of_keeps k12 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (diag1_ok s₁₂ (readSrc_sc hs₁₂ (by omega))) fun s₁₃ ⟨⟨c13, e13, f13⟩, k13⟩ => ?_
  have hs₁₃ := hs₁₂.of_keeps k13 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sbbMask_ok s₁₃ f13) fun s₁₄ ⟨m14, k14⟩ => ?_
  have hs₁₄ := hs₁₃.of_keeps k14 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (diagAdd_ok s₁₄ (readSrc_sc hs₁₄ (by omega)) (by decide) m14)
    fun s₁₅ ⟨⟨c15, e15, f15⟩, k15⟩ => ?_
  have hs₁₅ := hs₁₄.of_keeps k15 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sbbMask_ok s₁₅ f15) fun s₁₆ ⟨m16, k16⟩ => ?_
  have hs₁₆ := hs₁₅.of_keeps k16 (by decide)
  refine WP.mono (diagAdd_ok s₁₆ (readSrc_sc hs₁₆ (by omega)) (by decide) m16)
    fun s₁₇ ⟨⟨c17, e17, _⟩, k17⟩ => ?_
  refine ⟨?_,
    (k1.mono (by decide)).trans ((k2.mono (by decide)).trans ((k3.mono (by decide)).trans
    ((k4.mono (by decide)).trans ((k5.mono (by decide)).trans ((k6.mono (by decide)).trans
    ((k7.mono (by decide)).trans ((k8.mono (by decide)).trans ((k9.mono (by decide)).trans
    ((k10.mono (by decide)).trans ((k11.mono (by decide)).trans ((k12.mono (by decide)).trans
    ((k13.mono (by decide)).trans ((k14.mono (by decide)).trans ((k15.mono (by decide)).trans
    ((k16.mono (by decide)).trans (k17.mono (by decide)))))))))))))))))⟩
  -- Every register, as the step that last wrote it left it; memory is only read.
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, val3,
    reduceCtorEq, ite_false, ite_true] at e2 e7 e9 e12
  simp (disch := decide) only [k2.1, k3.1, k4.1, k5.1, k6.1, k7.1, k8.1, k9.1, k10.1,
    k12.1, k13.1, k14.1, k15.1, k16.1, k17.1, k1.2.1, k2.2.1, k3.2.1, k4.2.1, k5.2.1, k6.2.1,
    k7.2.1, k8.2.1, k9.2.1, k10.2.1, k11.2.1, k12.2.1, k13.2.1, k14.2.1, k15.2.1, k16.2.1,
    a1, a2, a3, z3, z4, z5, z8, hz, Nat.mul_zero, Nat.add_zero]
    at e2 e6 e7 e9 e10 e11 e12 e13 e15 e17 ⊢
  have h01 : (word s.mem base a).toNat * (word s.mem base (a + 8)).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := (word s.mem base a).isLt; omega)
      (by have := (word s.mem base (a + 8)).isLt; omega)
  have h02 : (word s.mem base a).toNat * (word s.mem base (a + 16)).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := (word s.mem base a).isLt; omega)
      (by have := (word s.mem base (a + 16)).isLt; omega)
  have h03 : (word s.mem base a).toNat * (word s.mem base (a + 24)).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := (word s.mem base a).isLt; omega)
      (by have := (word s.mem base (a + 24)).isLt; omega)
  have h12 : (word s.mem base (a + 8)).toNat * (word s.mem base (a + 16)).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := (word s.mem base (a + 8)).isLt; omega)
      (by have := (word s.mem base (a + 16)).isLt; omega)
  have h13 : (word s.mem base (a + 8)).toNat * (word s.mem base (a + 24)).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := (word s.mem base (a + 8)).isLt; omega)
      (by have := (word s.mem base (a + 24)).isLt; omega)
  have h23 : (word s.mem base (a + 16)).toNat * (word s.mem base (a + 24)).toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := (word s.mem base (a + 16)).isLt; omega)
      (by have := (word s.mem base (a + 24)).isLt; omega)
  have hlt : fe s.mem base a * fe s.mem base a < 2 ^ 256 * 2 ^ 256 :=
    Nat.mul_lt_mul'' (val4_lt _ _ _ _) (val4_lt _ _ _ _)
  simp only [X86_64.fe, val4] at hlt ⊢
  rw [sq_words] at hlt ⊢
  generalize (word s.mem base a).toNat * (word s.mem base (a + 8)).toNat = p01 at *
  generalize (word s.mem base a).toNat * (word s.mem base (a + 16)).toNat = p02 at *
  generalize (word s.mem base a).toNat * (word s.mem base (a + 24)).toNat = p03 at *
  generalize (word s.mem base (a + 8)).toNat * (word s.mem base (a + 16)).toNat = p12 at *
  generalize (word s.mem base (a + 8)).toNat * (word s.mem base (a + 24)).toNat = p13 at *
  generalize (word s.mem base (a + 16)).toNat * (word s.mem base (a + 24)).toNat = p23 at *
  generalize (word s.mem base a).toNat * (word s.mem base a).toNat = p00 at *
  generalize (word s.mem base (a + 8)).toNat * (word s.mem base (a + 8)).toNat = p11 at *
  generalize (word s.mem base (a + 16)).toNat * (word s.mem base (a + 16)).toNat = p22 at *
  generalize (word s.mem base (a + 24)).toNat * (word s.mem base (a + 24)).toNat = p33 at *
  have h6 : c6.toNat = 0 := by
    have := Bool.toNat_le c6; have := (s₂.gpr .r10).isLt
    omega_using [e6, h02]
  rw [h6, Nat.mul_zero, Nat.add_zero] at e6
  have cross : (s₂.gpr .r9).toNat + 2 ^ 64 * (s₆.gpr .r10).toNat +
      2 ^ 128 * (s₇.gpr .r11).toNat + 2 ^ 192 * (s₉.gpr .r12).toNat +
      2 ^ 256 * (s₁₀.gpr .r13).toNat + 2 ^ 256 * (2 ^ 64 * (s₁₀.gpr .r14).toNat) +
      2 ^ 256 * (2 ^ 128 * c10.toNat) =
      p01 + 2 ^ 64 * p02 + 2 ^ 128 * (p03 + p12) + 2 ^ 192 * p13 + 2 ^ 256 * p23 := by
    omega_using [e2, e6, e7, e9, e10]
  have h10 : c10.toNat = 0 := by
    have := Bool.toNat_le c10
    omega_using [cross, h01, h02, h03, h12, h13, h23]
  rw [h10, Nat.mul_zero, Nat.add_zero] at cross
  have tot : (s₁₂.gpr .r8).toNat + 2 ^ 64 * (s₁₃.gpr .r9).toNat +
      2 ^ 128 * (s₁₃.gpr .r10).toNat + 2 ^ 192 * (s₁₃.gpr .r11).toNat +
      2 ^ 256 * ((s₁₅.gpr .r12).toNat + 2 ^ 64 * (s₁₅.gpr .r13).toNat +
        2 ^ 128 * (s₁₇.gpr .r14).toNat + 2 ^ 192 * (s₁₇.gpr .r15).toNat) +
      2 ^ 256 * (2 ^ 256 * c17.toNat) =
      p00 + 2 ^ 128 * p11 + 2 ^ 256 * p22 + 2 ^ 256 * (2 ^ 128 * p33) +
        2 * (2 ^ 64 * p01 + 2 ^ 128 * p02 + 2 ^ 192 * p03 + 2 ^ 192 * p12 + 2 ^ 256 * p13 +
          2 ^ 256 * (2 ^ 64 * p23)) := by
    omega_using [cross, e11, e12, e13, e15, e17]
  have h17 := Bool.toNat_le c17
  omega_using [tot, hlt, h17]



/-- `[o] = [a]²`, at most `2p`. -/
theorem sqrBnd_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (ho : Slot o)
    (ha : Slot a) :
    WP isa (.block (sqr o a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base a ∧
        fe s'.mem base o ≤ 2 * VG.Spec.X25519.P := by
  rw [show sqr o a = sqrProd a ++ (reduceC ++ store4 o) by
    simp only [sqr, sqrProd, List.append_assoc], WP.block_append_iff]
  refine WP.mono (sqrProd_ok hs ha) fun s₁ ⟨e1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduceC_ok s₁) fun s₂ ⟨e2, b2, k2⟩ => ?_
  have K := k1.trans (k2.mono (by decide))
  refine WP.mono (store4_ok (hs.of_keeps K (by decide)) ho) fun s₃ ⟨m3, g3, rd3, wr3⟩ => ?_
  refine ⟨⟨fun r hr => (g3 r).trans (K.1 r hr), rd3.trans K.2.2.1, wr3.trans K.2.2.2, ?_⟩, ?_,
    by rw [m3, fe_st4 _ _ (by omega)]; exact b2⟩
  · rw [m3, K.2.1]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_mul
    rw [m3, fe_st4 _ _ (by omega), e2, e1]

/-- `[o] = 2 · [a]²`. -/
theorem sqr2_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (ho : Slot o)
    (ha : Slot a) :
    WP isa (.block (sqr2 o a)) s fun s' => Op base o s s' ∧
      F s'.mem base o = F s.mem base a * F s.mem base a + F s.mem base a * F s.mem base a := by
  rw [show sqr2 o a = sqrProd a ++ (reduceC2 ++ store4 o) by
    simp only [sqr2, sqrProd, List.append_assoc], WP.block_append_iff]
  refine WP.mono (sqrProd_ok hs ha) fun s₁ ⟨e1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduceC2_ok s₁) fun s₂ ⟨e2, k2⟩ => ?_
  have K := k1.trans (k2.mono (by decide))
  refine WP.mono (store4_ok (hs.of_keeps K (by decide)) ho) fun s₃ ⟨m3, g3, rd3, wr3⟩ => ?_
  refine ⟨⟨fun r hr => (g3 r).trans (K.1 r hr), rd3.trans K.2.2.1, wr3.trans K.2.2.2, ?_⟩, ?_⟩
  · rw [m3, K.2.1]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_mul2
    rw [m3, fe_st4 _ _ (by omega), e2, e1]

/-- `[o] = [a]²`. -/
theorem sqr_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat} (ho : Slot o)
    (ha : Slot a) :
    WP isa (.block (sqr o a)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base a :=
  WP.mono (sqrBnd_ok hs ho ha) fun _ ⟨h, e, _⟩ => ⟨h, e⟩

end VG.Proof.X25519.X86_64
