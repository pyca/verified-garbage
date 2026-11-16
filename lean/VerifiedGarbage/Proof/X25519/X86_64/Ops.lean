module

public import VerifiedGarbage.Proof.X25519.X86_64.Mem
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.X25519.Field

/-! ### `X25519.X86_64.Mul`, which only this module used -/

section

/-!
# X25519 on x86-64: multiplication

A row of a product (`row`, which Ed25519's scalar arithmetic uses), for any
five registers, from four multiply-accumulate steps (`mulStep_ok`); the
reduction of an eight-word product (`reduceC`); and a column of products
(`accCol`).
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64

/-- A row of a product, into the registers `r0`–`r4`. -/
def rowR (a b i : Nat) (r0 r1 r2 r3 r4 : Reg) : List Instr :=
  [.mov .rcx (.mem (sc (a + 8 * i))), .mov32 .rbp (.imm 0)] ++
    (mulStep r0 .rbp .rcx (.mem (sc (b + 8 * 0))) ++ (mulStep r1 .rbp .rcx (.mem (sc (b + 8 * 1))) ++
      (mulStep r2 .rbp .rcx (.mem (sc (b + 8 * 2))) ++ (mulStep r3 .rbp .rcx (.mem (sc (b + 8 * 3))) ++
        [.mov r4 (.reg .rbp)]))))

theorem row_eq (a b i : Nat) :
    row a b i = rowR a b i (t i) (t (i + 1)) (t (i + 2)) (t (i + 3)) (t (i + 4)) := by
  simp only [row, rowR, List.append_assoc]
  rfl

/-- The start of a row: `rcx = a_i`, `rbp = 0`. -/
theorem rowStart_ok {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 4096) :
    WP isa (.block [.mov .rcx (.mem (sc d)), .mov32 .rbp (.imm 0)]) s fun s' =>
      s'.gpr .rcx = word s.mem base d ∧ s'.gpr .rbp = 0 ∧ Keeps [.rcx, .rbp] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc_sc hs hd, readSrc32,
    Option.map_some, State.setReg32, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq,
    Option.some.injEq, exists_eq_left']
  refine ⟨by trivial, by trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

/-- A row: `r0 + 2⁶⁴ r1 + 2¹²⁸ r2 + 2¹⁹² r3 + a_i · b`, into `r0`–`r4`. -/
theorem rowR_ok {s : State} {base : Addr} (hs : Scr s base) {a b i : Nat}
    (ha : a + 8 * i + 8 ≤ 4096) (hb : b + 32 ≤ 4096) {r0 r1 r2 r3 r4 : Reg}
    (hd : ([r0, r1, r2, r3, r4, .rax, .rdx, .rcx, .rbp, .rdi] : List Reg).Nodup) :
    WP isa (.block (rowR a b i r0 r1 r2 r3 r4)) s fun s' =>
      val4 (s'.gpr r0) (s'.gpr r1) (s'.gpr r2) (s'.gpr r3) + 2 ^ 256 * (s'.gpr r4).toNat =
        val4 (s.gpr r0) (s.gpr r1) (s.gpr r2) (s.gpr r3) +
          (word s.mem base (a + 8 * i)).toNat * fe s.mem base b ∧
      Keeps [r0, r1, r2, r3, r4, .rax, .rdx, .rcx, .rbp] s s' := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h02, h03, h04, h0a, h0d, h0c, h0b, h0i⟩, ⟨h12, h13, h14, h1a, h1d, h1c, h1b, h1i⟩,
    ⟨h23, h24, h2a, h2d, h2c, h2b, h2i⟩, ⟨h34, h3a, h3d, h3c, h3b, h3i⟩,
    ⟨h4a, h4d, h4c, h4b, h4i⟩, -⟩ := hd
  rw [rowR, WP.block_append_iff]
  refine WP.mono (rowStart_ok hs (by omega_arith)) fun s₁ ⟨c1, b1, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₁ (readSrc_sc hs₁ (by omega_arith)) h0a h0d (by decide) (by decide)
    (by decide) h0b) fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by simp [Ne.symm h0i])
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₂ (readSrc_sc hs₂ (by omega_arith)) h1a h1d (by decide) (by decide)
    (by decide) h1b) fun s₃ ⟨e3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by simp [Ne.symm h1i])
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₃ (readSrc_sc hs₃ (by omega_arith)) h2a h2d (by decide) (by decide)
    (by decide) h2b) fun s₄ ⟨e4, k4⟩ => ?_
  have hs₄ := hs₃.of_keeps k4 (by simp [Ne.symm h2i])
  rw [WP.block_append_iff]
  refine WP.mono (mulStep_ok s₄ (readSrc_sc hs₄ (by omega_arith)) h3a h3d (by decide) (by decide)
    (by decide) h3b) fun s₅ ⟨e5, k5⟩ => ?_
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, Option.map_some,
    Option.some.injEq, exists_eq_left', RegUpd.gpr_setReg_self]
  -- The memory and the registers along the way.
  have M1 : s₁.mem = s.mem := k1.2.1
  have M2 : s₂.mem = s.mem := k2.2.1.trans M1
  have M3 : s₃.mem = s.mem := k3.2.1.trans M2
  have M4 : s₄.mem = s.mem := k4.2.1.trans M3
  have C2 : s₂.gpr .rcx = s₁.gpr .rcx := k2.1 _ (by simp [Ne.symm h0c])
  have C3 : s₃.gpr .rcx = s₁.gpr .rcx := (k3.1 _ (by simp [Ne.symm h1c])).trans C2
  have C4 : s₄.gpr .rcx = s₁.gpr .rcx := (k4.1 _ (by simp [Ne.symm h2c])).trans C3
  have r0_1 : s₁.gpr r0 = s.gpr r0 := k1.1 _ (by simp [h0c, h0b])
  have r0_5 : s₅.gpr r0 = s₂.gpr r0 := by
    rw [k5.1 _ (by simp [h03, h0b, h0a, h0d]), k4.1 _ (by simp [h02, h0b, h0a, h0d]),
      k3.1 _ (by simp [h01, h0b, h0a, h0d])]
  have r1_2 : s₂.gpr r1 = s.gpr r1 := by
    rw [k2.1 _ (by simp [Ne.symm h01, h1b, h1a, h1d]), k1.1 _ (by simp [h1c, h1b])]
  have r1_5 : s₅.gpr r1 = s₃.gpr r1 := by
    rw [k5.1 _ (by simp [h13, h1b, h1a, h1d]), k4.1 _ (by simp [h12, h1b, h1a, h1d])]
  have r2_3 : s₃.gpr r2 = s.gpr r2 := by
    rw [k3.1 _ (by simp [Ne.symm h12, h2b, h2a, h2d]), k2.1 _ (by simp [Ne.symm h02, h2b, h2a, h2d]),
      k1.1 _ (by simp [h2c, h2b])]
  have r2_5 : s₅.gpr r2 = s₄.gpr r2 := k5.1 _ (by simp [h23, h2b, h2a, h2d])
  have r3_4 : s₄.gpr r3 = s.gpr r3 := by
    rw [k4.1 _ (by simp [Ne.symm h23, h3b, h3a, h3d]), k3.1 _ (by simp [Ne.symm h13, h3b, h3a, h3d]),
      k2.1 _ (by simp [Ne.symm h03, h3b, h3a, h3d]), k1.1 _ (by simp [h3c, h3b])]
  refine ⟨?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have z : (0 : BitVec 64).toNat = 0 := rfl
    simp only [M1, M2, M3, M4, C2, C3, C4, c1, b1, r0_1, r1_2, r2_3, r3_4, z, Nat.mul_zero,
      Nat.add_zero, Nat.mul_one, Nat.reduceMul, word] at e2 e3 e4 e5
    simp only [val4, fe, word, RegUpd.gpr_setReg_of_ne _ _ h04, RegUpd.gpr_setReg_of_ne _ _ h14,
      RegUpd.gpr_setReg_of_ne _ _ h24, RegUpd.gpr_setReg_of_ne _ _ h34, r0_5, r1_5, r2_5]
    have hp : ∀ x y z w v : Nat, v * (x + 2 ^ 64 * y + 2 ^ 128 * z + 2 ^ 192 * w) =
        v * x + 2 ^ 64 * (v * y) + 2 ^ 128 * (v * z) + 2 ^ 192 * (v * w) := by intros; grind
    rw [hp]
    omega_arith
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2.2.1]
    rw [k5.1 _ (by simp [hr.2.2.2.1, hr.2.2.2.2.2.2.2.2, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]),
      k4.1 _ (by simp [hr.2.2.1, hr.2.2.2.2.2.2.2.2, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]),
      k3.1 _ (by simp [hr.2.1, hr.2.2.2.2.2.2.2.2, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]),
      k2.1 _ (by simp [hr.1, hr.2.2.2.2.2.2.2.2, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1]),
      k1.1 _ (by simp [hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2])]
  · exact k5.2.1.trans M4
  · rw [RegUpd.rd_setReg, k5.2.2.1, k4.2.2.1, k3.2.2.1, k2.2.2.1, k1.2.2.1]
  · rw [RegUpd.wr_setReg, k5.2.2.2, k4.2.2.2, k3.2.2.2, k2.2.2.2, k1.2.2.2]

/-! ## The reduction, and columns of products -/

/-- A carry subtracted as its mask (`sbb x, x`): added. -/
theorem sub_mask (h : BitVec 64) (c : Bool) (hh : h.toNat + 1 < 2 ^ 64) :
    (h - (0#64 - (BitVec.ofBool c).setWidth 64)).toNat = h.toNat + c.toNat := by
  have hc := Bool.toNat_le c
  rw [BitVec.zero_sub, BitVec.sub_neg, BitVec.toNat_add, toNat_ofBool]
  exact Nat.mod_eq_of_lt (by omega_arith)

/-- `38 h`, as `mul` leaves it: its high half is at most 37. -/
theorem mul38_halves (h k : BitVec 64) (hk : k.toNat = 38) :
    (BitVec.ofNat 64 (h.toNat * k.toNat)).toNat +
        2 ^ 64 * (BitVec.ofNat 64 (h.toNat * k.toNat / 2 ^ 64)).toNat = 38 * h.toNat ∧
      (BitVec.ofNat 64 (h.toNat * k.toNat / 2 ^ 64)).toNat ≤ 37 := by
  have hh := h.isLt
  rw [hk, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := _ / 2 ^ 64) (by omega_arith)]
  constructor <;> omega_arith

theorem redStep_ok (s : State) {t0 t1 h : Reg} {c : Bool}
    (hd : ([t0, t1, .rax, .rdx, .rbp] : List Reg).Nodup)
    (hk : (s.gpr .rcx).toNat = 38) (hm : s.gpr .rbp = 0#64 - (BitVec.ofBool c).setWidth 64) :
    WP isa (.block (redStep t0 t1 h)) s fun s' =>
      (∃ c' : Bool, (s'.gpr t0).toNat + 2 ^ 64 * (s'.gpr t1).toNat + 2 ^ 128 * c'.toNat =
          (s.gpr t0).toNat + 2 ^ 64 * (s.gpr t1).toNat + 38 * (s.gpr h).toNat + 2 ^ 64 * c.toNat ∧
        s'.gpr .rbp = 0#64 - (BitVec.ofBool c').setWidth 64) ∧
      Keeps [t0, t1, .rax, .rdx, .rbp] s s' := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨h01, h0a, h0d, h0b⟩, ⟨h1a, h1d, h1b⟩, -⟩ := hd
  apply WP.of_runBlock
  simp only [redStep, runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc, execMul, execAlu,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
    exists_eq_left', h01, Ne.symm h01, h0a, h0d, h0b, h1a, h1d, h1b, Ne.symm h0d,
    Ne.symm h0b, Ne.symm h1b, BitVec.sub_self, hm]
  obtain ⟨hmul, hhi⟩ := mul38_halves (s.gpr h) (s.gpr .rcx) hk
  generalize BitVec.ofNat 64 ((s.gpr h).toNat * (s.gpr .rcx).toNat / 2 ^ 64) = hi at hmul hhi ⊢
  generalize BitVec.ofNat 64 ((s.gpr h).toNat * (s.gpr .rcx).toNat) = lo at hmul ⊢
  have hs := sub_mask hi c (by omega_arith)
  generalize hi - (0#64 - (BitVec.ofBool c).setWidth 64) = d at hs ⊢
  have e0 := add_carry (s.gpr t0) lo
  have e1 := adc_carry (s.gpr t1) d (decide (2 ^ 64 ≤ (s.gpr t0).toNat + lo.toNat))
  generalize decide (2 ^ 64 ≤ (s.gpr t0).toNat + lo.toNat) = c0 at e0 e1 ⊢
  generalize decide (2 ^ 64 ≤ (s.gpr t1).toNat + d.toNat + c0.toNat) = c1 at e1 ⊢
  refine ⟨⟨c1, by omega_using [hmul, hs, e0, e1], rfl⟩, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1,
    hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- The start of `reduceLoC`: `38 r12` added at `r8, r9`. -/
theorem red0_ok (s : State) :
    WP isa (.block [.mov32 .rcx (.imm 38), .mov .rax (.reg .r12), .mul .rcx,
      .alu .add .r8 (.reg .rax), .alu .adc .r9 (.reg .rdx), .alu .sbb .rbp (.reg .rbp)]) s fun s' =>
      (s'.gpr .rcx).toNat = 38 ∧
      (∃ c' : Bool, (s'.gpr .r8).toNat + 2 ^ 64 * (s'.gpr .r9).toNat + 2 ^ 128 * c'.toNat =
          (s.gpr .r8).toNat + 2 ^ 64 * (s.gpr .r9).toNat + 38 * (s.gpr .r12).toNat ∧
        s'.gpr .rbp = 0#64 - (BitVec.ofBool c').setWidth 64) ∧
      Keeps [.r8, .r9, .rax, .rdx, .rcx, .rbp] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc, readSrc32, execMul,
    execAlu, State.setReg32, Option.map_some, Option.bind_some, RegUpd.gpr_setReg,
    RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true,
    ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left', BitVec.sub_self]
  have hk : ((38 : BitVec 32).setWidth 64).toNat = 38 := rfl
  obtain ⟨hmul, -⟩ := mul38_halves (s.gpr .r12) ((38 : BitVec 32).setWidth 64) hk
  generalize BitVec.ofNat 64 ((s.gpr .r12).toNat * ((38 : BitVec 32).setWidth 64).toNat / 2 ^ 64) = hi
    at hmul ⊢
  generalize BitVec.ofNat 64 ((s.gpr .r12).toNat * ((38 : BitVec 32).setWidth 64).toNat) = lo at hmul ⊢
  have e0 := add_carry (s.gpr .r8) lo
  have e1 := adc_carry (s.gpr .r9) hi (decide (2 ^ 64 ≤ (s.gpr .r8).toNat + lo.toNat))
  generalize decide (2 ^ 64 ≤ (s.gpr .r8).toNat + lo.toNat) = c0 at e0 e1 ⊢
  generalize decide (2 ^ 64 ≤ (s.gpr .r9).toNat + hi.toNat + c0.toNat) = c1 at e1 ⊢
  refine ⟨hk, ⟨c1, by omega_using [hmul, e0, e1], rfl⟩, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1,
    hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2, ite_false]

/-- The end of `reduceLoC`: `38 r15` and the carry added at `r11`, the word above into `r12`. -/
theorem redEnd_ok (s : State) {c : Bool} (hk : (s.gpr .rcx).toNat = 38)
    (hm : s.gpr .rbp = 0#64 - (BitVec.ofBool c).setWidth 64) :
    WP isa (.block [.mov .rax (.reg .r15), .mul .rcx, .alu .sub .rdx (.reg .rbp),
      .alu .add .r11 (.reg .rax), .alu .adc .rdx (.imm 0), .mov .r12 (.reg .rdx)]) s fun s' =>
      (s'.gpr .r11).toNat + 2 ^ 64 * (s'.gpr .r12).toNat =
        (s.gpr .r11).toNat + 38 * (s.gpr .r15).toNat + 2 ^ 64 * c.toNat ∧
      Keeps [.r11, .r12, .rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc, execMul, execAlu,
    Option.map_some, Option.bind_some, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.cf_arithFlags, RegUpd.cf_setReg, ite_true, ite_false,
    reduceCtorEq, Option.some.injEq, exists_eq_left', hm, se0]
  obtain ⟨hmul, hhi⟩ := mul38_halves (s.gpr .r15) (s.gpr .rcx) hk
  generalize BitVec.ofNat 64 ((s.gpr .r15).toNat * (s.gpr .rcx).toNat / 2 ^ 64) = hi at hmul hhi ⊢
  generalize BitVec.ofNat 64 ((s.gpr .r15).toNat * (s.gpr .rcx).toNat) = lo at hmul ⊢
  have hs := sub_mask hi c (by omega_arith)
  generalize hi - (0#64 - (BitVec.ofBool c).setWidth 64) = d at hs ⊢
  have hc := Bool.toNat_le c
  have e0 := add_carry (s.gpr .r11) lo
  have e1 := adc_carry d 0 (decide (2 ^ 64 ≤ (s.gpr .r11).toNat + lo.toNat))
  generalize decide (2 ^ 64 ≤ (s.gpr .r11).toNat + lo.toNat) = c0 at e0 e1 ⊢
  have hc0 := Bool.toNat_le c0
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  rw [hz, Nat.add_zero, show decide (2 ^ 64 ≤ d.toNat + c0.toNat) = false from
    decide_eq_false (by omega_arith), Bool.toNat_false, Nat.mul_zero, Nat.add_zero] at e1
  refine ⟨by omega_using [hmul, hs, e0, e1], fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.gpr_setFlags, hr.1, hr.2.1,
    hr.2.2.1, hr.2.2.2, ite_false]

/-- `reduceLoC`: `lo + 38 hi` of the eight words `r8–r15`, into `r8–r11` and the word `r12`. -/
theorem reduceLoC_ok (s : State) :
    WP isa (.block reduceLoC) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) + 2 ^ 256 * (s'.gpr .r12).toNat =
        val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
          38 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15) ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .rax, .rcx, .rdx, .rbp] s s' := by
  have g : ∀ {x y : State} {rs : List Reg} (k : Keeps rs x y) (r : Reg), r ∉ rs → y.gpr r = x.gpr r :=
    fun k r h => k.1 r h
  rw [reduceLoC, List.append_assoc, List.append_assoc, WP.block_append_iff]
  refine WP.mono (red0_ok s) fun s₁ ⟨k38, ⟨c1, e1, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (redStep_ok s₁ (by decide) k38 m1) fun s₂ ⟨⟨c2, e2, m2⟩, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (redStep_ok s₂ (by decide) ((congrArg _ (g k2 .rcx (by decide))).trans k38) m2)
    fun s₃ ⟨⟨c3, e3, m3⟩, k3⟩ => ?_
  refine WP.mono (redEnd_ok s₃ ((congrArg _ ((g k3 .rcx (by decide)).trans
    (g k2 .rcx (by decide)))).trans k38) m3) fun s₄ ⟨e4, k4⟩ => ?_
  refine ⟨?_, (((k1.mono (by decide)).trans (k2.mono (by decide))).trans (k3.mono (by decide))).trans
    (k4.mono (by decide))⟩
  rw [g k1 .r13 (by decide), g k1 .r10 (by decide)] at e2
  rw [g k2 .r14 (by decide), g k1 .r14 (by decide), g k2 .r11 (by decide),
    g k1 .r11 (by decide)] at e3
  rw [g k3 .r15 (by decide), g k2 .r15 (by decide), g k1 .r15 (by decide)] at e4
  simp only [val4, g k4 .r8 (by decide), g k3 .r8 (by decide), g k2 .r8 (by decide),
    g k4 .r9 (by decide), g k3 .r9 (by decide), g k4 .r10 (by decide)]
  omega_using [e1, e2, e3, e4]

open VG.Spec.X25519 (P) in
/-- `reduceC`: `r8–r11 + 2²⁵⁶ r12–r15`, reduced into `r8–r11` (modulo `p`), at most `2p`. -/
theorem reduceC_ok (s : State) :
    WP isa (.block reduceC) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) % P =
        (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
          2 ^ 256 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15)) % P ∧
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) ≤ 2 * P ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .rax, .rcx, .rdx, .rbp] s s' := by
  rw [reduceC, WP.block_append_iff]
  refine WP.mono (reduceLoC_ok s) fun s₁ ⟨hv, k1⟩ => ?_
  have h12 : (s₁.gpr .r12).toNat < 39 := by
    simp only [val4] at hv
    have := (s.gpr .r8).isLt; have := (s.gpr .r9).isLt; have := (s.gpr .r10).isLt
    have := (s.gpr .r11).isLt; have := (s.gpr .r12).isLt; have := (s.gpr .r13).isLt
    have := (s.gpr .r14).isLt; have := (s.gpr .r15).isLt
    have := (s₁.gpr .r8).isLt; have := (s₁.gpr .r9).isLt; have := (s₁.gpr .r10).isLt
    have := (s₁.gpr .r11).isLt
    omega_arith
  refine WP.mono (fold19X_ok s₁ (by omega_using [h12])) fun s₂ ⟨e2, b2, k2⟩ => ?_
  refine ⟨?_, b2, k1.trans (k2.mono (by decide))⟩
  rw [e2, hv, fold256]

/-- `loads`: four words of the working space into four registers. -/
theorem loads_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : o + 32 ≤ 4096)
    {a b c d : Reg} (hd : ([a, b, c, d, .rdi] : List Reg).Nodup) :
    WP isa (.block (loads o a b c d)) s fun s' =>
      s'.gpr a = word s.mem base o ∧ s'.gpr b = word s.mem base (o + 8) ∧
      s'.gpr c = word s.mem base (o + 16) ∧ s'.gpr d = word s.mem base (o + 24) ∧
      Keeps [a, b, c, d] s s' := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  obtain ⟨⟨hab, hac, had, hai⟩, ⟨hbc, hbd, hbi⟩, ⟨hcd, hci⟩, hdi⟩ := hd
  have L : ∀ e, e + 8 ≤ 4096 → InRegions (s.rd ++ s.wr) (off base e) 8 :=
    fun e he => ⟨_, List.mem_append_right _ hs.wr, contains_sc he⟩
  apply WP.of_runBlock
  simp only [loads, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64, ea_sc,
    RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg, hs.rdi,
    L o (by omega), L (o + 8) (by omega), L (o + 16) (by omega), L (o + 24) (by omega), ite_true,
    ite_false, Ne.symm hai, Ne.symm hbi, Ne.symm hci, hab, hac, had, hbc, hbd, hcd,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

/-- A column of products: each added to the column's three words, whose highest counts the
carries. -/
theorem accCol_ok {base : Addr} {t0 t1 t2 : Reg}
    (hd : ([t0, t1, t2, .rax, .rdx] : List Reg).Nodup) (hi : .rdi ∉ [t0, t1, t2, .rax, .rdx]) :
    ∀ (ps : List (Reg × Nat)) (s : State), Scr s base →
      (∀ p ∈ ps, p.1 ∉ [t0, t1, t2, .rax, .rdx] ∧ p.2 + 8 ≤ 4096) →
      (s.gpr t2).toNat + ps.length < 2 ^ 64 →
      WP isa (.block (accCol t0 t1 t2 ps)) s fun s' =>
        val3 (s'.gpr t0) (s'.gpr t1) (s'.gpr t2) = val3 (s.gpr t0) (s.gpr t1) (s.gpr t2) +
          (ps.map fun p => (word s.mem base p.2).toNat * (s.gpr p.1).toNat).sum ∧
        (s'.gpr t2).toNat ≤ (s.gpr t2).toNat + ps.length ∧
        Keeps [t0, t1, t2, .rax, .rdx] s s'
  | [], s, _, _, _ => by
    apply WP.of_runBlock
    simp only [accCol, List.flatMap_nil, runBlock_nil, Option.some.injEq, exists_eq_left']
    exact ⟨rfl, Nat.le_refl _, fun _ _ => rfl, rfl, rfl, rfl⟩
  | p :: ps, s, hs, hp, h2 => by
    have hp0 := hp p List.mem_cons_self
    rw [accCol, List.flatMap_cons, WP.block_append_iff]
    refine WP.mono (acc3_ok s (readSrc_sc hs hp0.2) hd
      (fun h => hp0.1 (by rw [h]; simp)) (by simp only [List.length_cons] at h2; omega))
      fun s₁ ⟨e1, b1, k1⟩ => ?_
    refine WP.mono (accCol_ok hd hi ps s₁ (hs.of_keeps k1 hi)
      (fun q hq => hp q (List.mem_cons_of_mem _ hq))
      (by simp only [List.length_cons] at h2; omega)) fun s₂ ⟨e2, b2, k2⟩ => ?_
    refine ⟨?_, by simp only [List.length_cons]; omega, k1.trans k2⟩
    have hm : (ps.map fun q => (word s₁.mem base q.2).toNat * (s₁.gpr q.1).toNat) =
        ps.map fun q => (word s.mem base q.2).toNat * (s.gpr q.1).toNat :=
      List.map_congr_left fun q hq => by
        rw [k1.2.1, k1.1 q.1 (hp q (List.mem_cons_of_mem _ hq)).1]
    rw [e2, hm, e1, List.map_cons, List.sum_cons]
    omega

end VG.Proof.X25519.X86_64

end

end


/-!
# X25519 on x86-64: the field operations

Each field operation on the working space (`mul`, `mulSmall`, `add`, `sub`,
and `cswap`), as a change of the field elements `F` it reads and writes: the
element at `o` becomes the result, every byte outside it is unchanged, and so
are the registers but those the arithmetic uses (`Op`).
-/

@[expose] public section

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

/-- The field element at `base + o`, in `GF(p)`. -/
abbrev F (m : Mem) (base : Addr) (o : Nat) : Spec.X25519.Fe := toFe (fe m base o)

/-- The registers the field arithmetic uses. -/
def clob : List Reg := [.rax, .rcx, .rdx, .rbp, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

/-- A field operation's effect but for its result: the registers but `clob`,
the regions and the memory outside the 32 bytes at `base + o` are unchanged. -/
structure Op (base : Addr) (o : Nat) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ clob → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  mem : Outside base o 32 s.mem s'.mem

theorem Op.scr {base : Addr} {o : Nat} {s s' : State} (h : Op base o s s') (hs : Scr s base) :
    Scr s' base :=
  ⟨(h.gpr _ (by decide)).trans hs.rdi, h.wr ▸ hs.wr, hs.nowrap⟩

/-- A field element's slot: 32 bytes of the working space. -/
abbrev Slot (o : Nat) : Prop := o + 32 ≤ 4096

theorem stores_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : Slot o)
    (a b c d : Reg) :
    WP isa (.block (stores o a b c d)) s fun s' =>
      s'.mem = st4 s.mem base o (s.gpr a) (s.gpr b) (s.gpr c) (s.gpr d) ∧
      (∀ r, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have w : ∀ d, d + 8 ≤ 4096 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hs.wr, contains_sc hd⟩
  apply WP.of_runBlock
  simp only [stores, runBlock_cons, runStep_some, runBlock_nil, exec, ea_sc, hs.rdi, State.store64,
    w o (by omega), w (o + 8) (by omega), w (o + 16) (by omega), w (o + 24) (by omega), ite_true,
    Option.some.injEq, exists_eq_left']
  exact ⟨rfl, fun _ => trivial, trivial, trivial⟩

theorem store4_ok {s : State} {base : Addr} (hs : Scr s base) {o : Nat} (ho : Slot o) :
    WP isa (.block (store4 o)) s fun s' =>
      s'.mem = st4 s.mem base o (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) ∧
      (∀ r, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr :=
  stores_ok hs ho _ _ _ _

theorem zero4_ok (s : State) :
    WP isa (.block zero4) s fun s' =>
      s'.gpr .r8 = 0 ∧ s'.gpr .r9 = 0 ∧ s'.gpr .r10 = 0 ∧ s'.gpr .r11 = 0 ∧
      Keeps [.r8, .r9, .r10, .r11] s s' := by
  apply WP.of_runBlock
  simp only [zero4, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq, Option.some.injEq,
    exists_eq_left']
  refine ⟨rfl, rfl, rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem row0 (a b : Nat) : row a b 0 = rowR a b 0 .r8 .r9 .r10 .r11 .r12 := row_eq a b 0
theorem row1 (a b : Nat) : row a b 1 = rowR a b 1 .r9 .r10 .r11 .r12 .r13 := row_eq a b 1
theorem row2 (a b : Nat) : row a b 2 = rowR a b 2 .r10 .r11 .r12 .r13 .r14 := row_eq a b 2
theorem row3 (a b : Nat) : row a b 3 = rowR a b 3 .r11 .r12 .r13 .r14 .r15 := row_eq a b 3

theorem fe_mul_expand (m : Mem) (base : Addr) (a : Nat) (B : Nat) :
    fe m base a * B = (word m base (a + 8 * 0)).toNat * B + 2 ^ 64 * ((word m base (a + 8 * 1)).toNat * B) +
      2 ^ 128 * ((word m base (a + 8 * 2)).toNat * B) + 2 ^ 192 * ((word m base (a + 8 * 3)).toNat * B) := by
  simp only [X86_64.fe, val4, Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul, Nat.add_mul,
    Nat.mul_assoc]

/-- The product of two four-word numbers, by the products of their words (with no power of
two above `2²⁵⁶`). -/
theorem mul_words (x0 x1 x2 x3 y0 y1 y2 y3 : Nat) :
    (x0 + 2 ^ 64 * x1 + 2 ^ 128 * x2 + 2 ^ 192 * x3) * (y0 + 2 ^ 64 * y1 + 2 ^ 128 * y2 + 2 ^ 192 * y3) =
      x0 * y0 + 2 ^ 64 * (x0 * y1 + x1 * y0) + 2 ^ 128 * (x0 * y2 + x1 * y1 + x2 * y0) +
        2 ^ 192 * (x0 * y3 + x1 * y2 + x2 * y1 + x3 * y0) +
        2 ^ 256 * (x1 * y3 + x2 * y2 + x3 * y1 + 2 ^ 64 * (x2 * y3 + x3 * y2) +
          2 ^ 128 * (x3 * y3)) := by
  grind

/-- `mulProd`: the eight words of the product. -/
theorem mulProd_ok {s : State} {base : Addr} (hs : Scr s base) {a b : Nat} (ha : Slot a)
    (hb : Slot b) :
    WP isa (.block (mulProd a b)) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) +
          2 ^ 256 * val4 (s'.gpr .r12) (s'.gpr .r13) (s'.gpr .r14) (s'.gpr .r15) =
        fe s.mem base a * fe s.mem base b ∧ Keeps clob s s' := by
  have hz : (0 : BitVec 64).toNat = 0 := rfl
  simp only [mulProd, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (loads_ok hs hb (by decide)) fun s₁ ⟨b0, b1, b2, b3, k1⟩ => ?_
  have hs₁ := hs.of_keeps k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (prod2_ok s₁ (b := .r14) (readSrc_sc hs₁ (by omega)) (by decide) (by decide))
    fun s₂ ⟨e2, k2⟩ => ?_
  have hs₂ := hs₁.of_keeps k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s₂ .r10) fun s₃ ⟨z3, k3⟩ => ?_
  have hs₃ := hs₂.of_keeps k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s₃ .r11) fun s₄ ⟨z4, k4⟩ => ?_
  have hs₄ := hs₃.of_keeps k4 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (acc2_ok s₄ (b := .r15) (readSrc_sc hs₄ (by omega)) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₅ ⟨⟨c5, e5⟩, k5⟩ => ?_
  have hs₅ := hs₄.of_keeps k5 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (accCol_ok (by decide) (by decide) _ s₅ hs₅
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
        and_intros <;> first | decide | omega)
    (by rw [k5.1 .r11 (by decide), z4]; simp only [List.length_cons, List.length_nil]; decide)) fun s₆ ⟨e6, _, k6⟩ => ?_
  have hs₆ := hs₅.of_keeps k6 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s₆ .r12) fun s₇ ⟨z7, k7⟩ => ?_
  have hs₇ := hs₆.of_keeps k7 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (accCol_ok (by decide) (by decide) _ s₇ hs₇
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        and_intros <;> first | decide | omega)
    (by rw [z7]; simp only [List.length_cons, List.length_nil]; decide)) fun s₈ ⟨e8, _, k8⟩ => ?_
  have hs₈ := hs₇.of_keeps k8 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s₈ .r13) fun s₉ ⟨z9, k9⟩ => ?_
  have hs₉ := hs₈.of_keeps k9 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (accCol_ok (by decide) (by decide) _ s₉ hs₉
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        and_intros <;> first | decide | omega)
    (by rw [z9]; simp only [List.length_cons, List.length_nil]; decide)) fun s₁₀ ⟨e10, _, k10⟩ => ?_
  have hs₁₀ := hs₉.of_keeps k10 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s₁₀ .r14) fun s₁₁ ⟨z11, k11⟩ => ?_
  have hs₁₁ := hs₁₀.of_keeps k11 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (accCol_ok (by decide) (by decide) _ s₁₁ hs₁₁
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        and_intros <;> first | decide | omega)
    (by rw [z11]; simp only [List.length_cons, List.length_nil]; decide)) fun s₁₂ ⟨e12, _, k12⟩ => ?_
  have hs₁₂ := hs₁₁.of_keeps k12 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (zero_ok s₁₂ .r15) fun s₁₃ ⟨z13, k13⟩ => ?_
  have hs₁₃ := hs₁₂.of_keeps k13 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (accCol_ok (by decide) (by decide) _ s₁₃ hs₁₃
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        and_intros <;> first | decide | omega)
    (by rw [z13]; simp only [List.length_cons, List.length_nil]; decide)) fun s₁₄ ⟨e14, _, k14⟩ => ?_
  have hs₁₄ := hs₁₃.of_keeps k14 (by decide)
  refine WP.mono (acc2_ok s₁₄ (b := .rbp) (readSrc_sc hs₁₄ (by omega)) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)) fun s₁₅ ⟨⟨c15, e15⟩, k15⟩ => ?_
  refine ⟨?_,
    (k1.mono (by decide)).trans ((k2.mono (by decide)).trans ((k3.mono (by decide)).trans
    ((k4.mono (by decide)).trans ((k5.mono (by decide)).trans ((k6.mono (by decide)).trans
    ((k7.mono (by decide)).trans ((k8.mono (by decide)).trans ((k9.mono (by decide)).trans
    ((k10.mono (by decide)).trans ((k11.mono (by decide)).trans ((k12.mono (by decide)).trans
    ((k13.mono (by decide)).trans ((k14.mono (by decide)).trans
    (k15.mono (by decide)))))))))))))))⟩
  -- Every register, as the step that last wrote it left it; memory is only read.
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, val3,
    reduceCtorEq, ite_false] at e2 e6 e8 e10 e12 e14
  simp (disch := decide) only [k2.1, k3.1, k4.1, k5.1, k6.1, k7.1, k8.1, k9.1, k10.1, k11.1,
    k12.1, k13.1, k14.1, k15.1, k1.2.1, k2.2.1, k3.2.1, k4.2.1, k5.2.1, k6.2.1, k7.2.1, k8.2.1,
    k9.2.1, k10.2.1, k11.2.1, k12.2.1, k13.2.1, k14.2.1, b0, b1, b2, b3, z3, z4, z7, z9, z11,
    z13, hz, Nat.mul_zero, Nat.add_zero] at e2 e5 e6 e8 e10 e12 e14 e15 ⊢
  have hp01 : (word s.mem base a).toNat * (word s.mem base (b + 8)).toNat ≤
      (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by have := (word s.mem base a).isLt; omega)
      (by have := (word s.mem base (b + 8)).isLt; omega)
  have h5 : c5.toNat = 0 := by
    have := Bool.toNat_le c5; have := (s₂.gpr .r9).isLt
    omega_using [e5, hp01]
  have hlt : fe s.mem base a * fe s.mem base b < 2 ^ 256 * 2 ^ 256 :=
    Nat.mul_lt_mul'' (val4_lt _ _ _ _) (val4_lt _ _ _ _)
  simp only [X86_64.fe, val4] at hlt ⊢
  rw [mul_words] at hlt ⊢
  rw [h5, Nat.mul_zero, Nat.add_zero] at e5
  generalize (word s.mem base a).toNat * (word s.mem base b).toNat = p00 at *
  generalize (word s.mem base a).toNat * (word s.mem base (b + 8)).toNat = p01 at *
  generalize (word s.mem base a).toNat * (word s.mem base (b + 16)).toNat = p02 at *
  generalize (word s.mem base a).toNat * (word s.mem base (b + 24)).toNat = p03 at *
  generalize (word s.mem base (a + 8)).toNat * (word s.mem base b).toNat = p10 at *
  generalize (word s.mem base (a + 8)).toNat * (word s.mem base (b + 8)).toNat = p11 at *
  generalize (word s.mem base (a + 8)).toNat * (word s.mem base (b + 16)).toNat = p12 at *
  generalize (word s.mem base (a + 8)).toNat * (word s.mem base (b + 24)).toNat = p13 at *
  generalize (word s.mem base (a + 16)).toNat * (word s.mem base b).toNat = p20 at *
  generalize (word s.mem base (a + 16)).toNat * (word s.mem base (b + 8)).toNat = p21 at *
  generalize (word s.mem base (a + 16)).toNat * (word s.mem base (b + 16)).toNat = p22 at *
  generalize (word s.mem base (a + 16)).toNat * (word s.mem base (b + 24)).toNat = p23 at *
  generalize (word s.mem base (a + 24)).toNat * (word s.mem base b).toNat = p30 at *
  generalize (word s.mem base (a + 24)).toNat * (word s.mem base (b + 8)).toNat = p31 at *
  generalize (word s.mem base (a + 24)).toNat * (word s.mem base (b + 16)).toNat = p32 at *
  generalize (word s.mem base (a + 24)).toNat * (word s.mem base (b + 24)).toNat = p33 at *
  have tot : (s₂.gpr .r8).toNat + 2 ^ 64 * (s₆.gpr .r9).toNat + 2 ^ 128 * (s₈.gpr .r10).toNat +
      2 ^ 192 * (s₁₀.gpr .r11).toNat + 2 ^ 256 * ((s₁₂.gpr .r12).toNat +
        2 ^ 64 * (s₁₄.gpr .r13).toNat + 2 ^ 128 * (s₁₅.gpr .r14).toNat +
        2 ^ 192 * (s₁₅.gpr .r15).toNat) + 2 ^ 256 * (2 ^ 256 * c15.toNat) =
      p00 + 2 ^ 64 * (p01 + p10) + 2 ^ 128 * (p02 + p11 + p20) +
        2 ^ 192 * (p03 + p12 + p21 + p30) +
        2 ^ 256 * (p13 + p22 + p31 + 2 ^ 64 * (p23 + p32) + 2 ^ 128 * p33) := by
    omega_using [e2, e5, e6, e8, e10, e12, e14, e15]
  have h15 := Bool.toNat_le c15
  omega_using [tot, hlt, h15]



open VG.Spec.X25519 (P) in
/-- `reduceC2`: twice `r8–r11 + 2²⁵⁶ r12–r15`, reduced into `r8–r11` (modulo `p`). -/
theorem reduceC2_ok (s : State) :
    WP isa (.block reduceC2) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) % P =
        (2 * (val4 (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11) +
          2 ^ 256 * val4 (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15))) % P ∧
      Keeps [.r8, .r9, .r10, .r11, .r12, .rax, .rcx, .rdx, .rbp] s s' := by
  rw [reduceC2, List.append_assoc, WP.block_append_iff]
  refine WP.mono (reduceLoC_ok s) fun s₁ ⟨hv, k1⟩ => ?_
  have h12 : (s₁.gpr .r12).toNat < 39 := by
    have v := val4_lt (s.gpr .r8) (s.gpr .r9) (s.gpr .r10) (s.gpr .r11)
    have w := val4_lt (s.gpr .r12) (s.gpr .r13) (s.gpr .r14) (s.gpr .r15)
    omega_using [hv, v, w]
  rw [WP.block_append_iff]
  refine WP.mono (dbl5_ok s₁ (by omega_using [h12])) fun s₂ ⟨e2, h2, k2⟩ => ?_
  refine WP.mono (fold19X_ok s₂ (by omega_using [h12, h2])) fun s₃ ⟨e3, _, k3⟩ => ?_
  refine ⟨?_, (k1.trans (k2.mono (by decide))).trans (k3.mono (by decide))⟩
  rw [e3, e2, hv, Nat.mul_mod, Nat.mul_mod (2 : Nat) (_ + 2 ^ 256 * _), fold256]

open VG.Spec.X25519 (P) in
/-- Twice a product. -/
theorem toFe_mul2 {a b c : Nat} (h : c % P = 2 * (a * b) % P) :
    toFe c = toFe a * toFe b + toFe a * toFe b := by
  rw [← toFe_mul (c := a * b) rfl]
  exact toFe_add (by rw [h, Nat.two_mul])


/-- `[o] = [a] · [b]`, at most `2p`. -/
theorem mulBnd_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (mul o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base b ∧
        fe s'.mem base o ≤ 2 * VG.Spec.X25519.P := by
  rw [mul, List.append_assoc, WP.block_append_iff]
  refine WP.mono (mulProd_ok hs ha hb) fun s₁ ⟨e1, k1⟩ => ?_
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

/-- `[o] = 2 · [a] · [b]`. -/
theorem mul2_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (mul2 o a b)) s fun s' => Op base o s s' ∧
      F s'.mem base o = F s.mem base a * F s.mem base b + F s.mem base a * F s.mem base b := by
  rw [mul2, List.append_assoc, WP.block_append_iff]
  refine WP.mono (mulProd_ok hs ha hb) fun s₁ ⟨e1, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (reduceC2_ok s₁) fun s₂ ⟨e2, k2⟩ => ?_
  have K := k1.trans (k2.mono (by decide))
  refine WP.mono (store4_ok (hs.of_keeps K (by decide)) ho) fun s₃ ⟨m3, g3, rd3, wr3⟩ => ?_
  refine ⟨⟨fun r hr => (g3 r).trans (K.1 r hr), rd3.trans K.2.2.1, wr3.trans K.2.2.2, ?_⟩, ?_⟩
  · rw [m3, K.2.1]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [F]
    apply toFe_mul2
    rw [m3, fe_st4 _ _ (by omega), e2, e1]

/-- `[o] = [a] · [b]`. -/
theorem mul_ok {s : State} {base : Addr} (hs : Scr s base) {o a b : Nat} (ho : Slot o)
    (ha : Slot a) (hb : Slot b) :
    WP isa (.block (mul o a b)) s fun s' =>
      Op base o s s' ∧ F s'.mem base o = F s.mem base a * F s.mem base b :=
  WP.mono (mulBnd_ok hs ho ha hb) fun _ ⟨h, e, _⟩ => ⟨h, e⟩

end VG.Proof.X25519.X86_64
