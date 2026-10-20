module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Row
public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Math
import VerifiedGarbage.Proof.X25519.AArch64.Ops
import VerifiedGarbage.Proof.X25519.AArch64.Alt.Exec
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow

/-! # The inversion's rows' results

`shift o t`: the five words at `t` shifted right by 59, four words at `o`
(`shift_ok`). -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Inv

open VG VG.AArch64 VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64 (KeepRegs)
open VG.Impl.Ed25519.AArch64 (ld st)
open VG.Impl.Ed25519.AArch64.Divstep (shift reduce)
open VG.Proof.X25519.AArch64 (exec_lsr exec_lsl exec_sub_x exec_add_x exec_and_x)
open VG.Proof.X25519.AArch64.Alt (exec_mul_x exec_umulh_x exec_adds_x exec_adcs_x exec_adc_x)

variable {large : Bool}

theorem exec_extr_x (s : State) (d n m : Reg) {lsb : Nat} (h : lsb < 64) :
    exec (.extr .x d n m lsb) s = some (s.write .x d ((s.gpr n ++ s.gpr m).extractLsb' lsb 64)) := by
  rw [exec_extr h]
  simp only [State.read, BitVec.setWidth_eq, Size.bits]

/-- The words of a shift by 59. -/
theorem shift_arith (w0 w1 w2 w3 w4 : Nat) (h0 : w0 < 2 ^ 64) (h1 : w1 < 2 ^ 64)
    (h2 : w2 < 2 ^ 64) :
    (w1 * 2 ^ 64 + w0) / 2 ^ 59 % 2 ^ 64 + 2 ^ 64 * ((w2 * 2 ^ 64 + w1) / 2 ^ 59 % 2 ^ 64) +
        2 ^ 128 * ((w3 * 2 ^ 64 + w2) / 2 ^ 59 % 2 ^ 64) +
        2 ^ 192 * ((w4 * 2 ^ 64 + w3) / 2 ^ 59 % 2 ^ 64) =
      (w0 + 2 ^ 64 * w1 + 2 ^ 128 * w2 + 2 ^ 192 * w3 + 2 ^ 256 * w4) / 2 ^ 59 % 2 ^ 256 := by
  omega

/-- The five words at `t` into `x1`–`x3`, `x8`, `x9`. -/
theorem ld5_ok {s : State} {base : Addr} (hs : Scr s base large) {t : Nat}
    (ht : t % 8 = 0 ∧ t + 40 ≤ workSize large) :
    WP isa (.block [ld .x1 t, ld .x2 (t + 8), ld .x3 (t + 16), ld .x8 (t + 24), ld .x9 (t + 32)]) s
      fun u => u.gpr .x1 = word s.mem base t ∧ u.gpr .x2 = word s.mem base (t + 8) ∧
        u.gpr .x3 = word s.mem base (t + 16) ∧ u.gpr .x8 = word s.mem base (t + 24) ∧
        u.gpr .x9 = word s.mem base (t + 32) ∧ Keeps [.x1, .x2, .x3, .x8, .x9] s u := by
  have w1 : Reg.x1 ≠ .x0 := by decide
  have w2 : Reg.x2 ≠ .x0 := by decide
  have w3 : Reg.x3 ≠ .x0 := by decide
  have w8 : Reg.x8 ≠ .x0 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    load_sc hs ht.1 (by omega), load_sc (hs.write w1 _) (d := t + 8) (by omega) (by omega),
    load_sc ((hs.write w1 _).write w2 _) (d := t + 16) (by omega) (by omega),
    load_sc (((hs.write w1 _).write w2 _).write w3 _) (d := t + 24) (by omega) (by omega),
    load_sc ((((hs.write w1 _).write w2 _).write w3 _).write w8 _) (d := t + 32) (by omega)
      (by omega), Option.some.injEq, exists_eq_left']
  simp only [RegUpd.mem_write, RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false,
    BitVec.setWidth_eq]
  refine ⟨trivial, trivial, trivial, trivial, trivial, ⟨fun r hr => ?_, by simp only [RegUpd.mem_write],
    by simp only [RegUpd.rd_write], by simp only [RegUpd.wr_write], by simp only [RegUpd.sp_write]⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2, ite_false]

/-- Four words from `x1`–`x3`, `x8` stored at `o`. -/
theorem st4w_ok {s : State} {base : Addr} (hs : Scr s base large) {o : Nat}
    (ho : o % 8 = 0 ∧ o + 32 ≤ workSize large) (a b c d : Reg) :
    WP isa (.block [st a o, st b (o + 8), st c (o + 16), st d (o + 24)]) s fun u =>
      u.mem = st4 s.mem base o (s.gpr a) (s.gpr b) (s.gpr c) (s.gpr d) ∧ KeepRegs [] s u := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, store_sc hs ho.1 (by omega),
    store_sc (hs.setMem _) (d := o + 8) (by omega) (by omega),
    store_sc ((hs.setMem _).setMem _) (d := o + 16) (by omega) (by omega),
    store_sc (((hs.setMem _).setMem _).setMem _) (d := o + 24) (by omega) (by omega),
    Option.some.injEq, exists_eq_left']
  exact ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

/-- The words loaded, shifted and stored. -/
theorem shift_ok {s : State} {base : Addr} (hs : Scr s base large) {o t : Nat}
    (ho : o % 8 = 0 ∧ o + 32 ≤ workSize large) (ht : t % 8 = 0 ∧ t + 40 ≤ workSize large) :
    WP isa (.block (shift o t)) s fun u =>
      fe u.mem base o = val5 s.mem base t / 2 ^ 59 % 2 ^ 256 ∧ Outside base o 32 s.mem u.mem ∧
      KeepRegs [.x1, .x2, .x3, .x8, .x9] s u := by
  have _hcap := workSize_le large
  change WP isa (.block (([ld .x1 t, ld .x2 (t + 8), ld .x3 (t + 16), ld .x8 (t + 24),
    ld .x9 (t + 32)] : List Instr) ++ (([.extr .x .x1 .x2 .x1 59, .extr .x .x2 .x3 .x2 59,
    .extr .x .x3 .x8 .x3 59, .extr .x .x8 .x9 .x8 59] : List Instr) ++
    ([st .x1 o, st .x2 (o + 8), st .x3 (o + 16), st .x8 (o + 24)] : List Instr)))) s _
  rw [WP.block_append_iff]
  refine WP.mono (ld5_ok hs ht) fun a ⟨a1, a2, a3, a8, a9, ka⟩ => ?_
  rw [WP.block_append_iff]
  have hx : WP isa (.block ([.extr .x .x1 .x2 .x1 59, .extr .x .x2 .x3 .x2 59,
      .extr .x .x3 .x8 .x3 59, .extr .x .x8 .x9 .x8 59] : List Instr)) a fun b =>
      b.gpr .x1 = (a.gpr .x2 ++ a.gpr .x1).extractLsb' 59 64 ∧
      b.gpr .x2 = (a.gpr .x3 ++ a.gpr .x2).extractLsb' 59 64 ∧
      b.gpr .x3 = (a.gpr .x8 ++ a.gpr .x3).extractLsb' 59 64 ∧
      b.gpr .x8 = (a.gpr .x9 ++ a.gpr .x8).extractLsb' 59 64 ∧ Keeps [.x1, .x2, .x3, .x8] a b := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_extr_x _ _ _ _ (by decide : 59 < 64),
      Option.some.injEq, exists_eq_left']
    simp only [RegUpd.gpr_write, reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq]
    refine ⟨trivial, trivial, trivial, trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]
  refine WP.mono hx fun b ⟨b1, b2, b3, b8, kb⟩ => ?_
  have hsb : Scr b base large := (hs.of_keeps ka (by decide)).of_keeps kb (by decide)
  refine WP.mono (st4w_ok hsb ho .x1 .x2 .x3 .x8) fun u ⟨mu, ku⟩ => ?_
  have mb : b.mem = s.mem := by rw [kb.mem, ka.mem]
  refine ⟨?_, ?_, ⟨fun r hr => ?_, by rw [ku.rd, kb.rd, ka.rd], by rw [ku.wr, kb.wr, ka.wr],
    by rw [ku.sp, kb.sp, ka.sp]⟩⟩
  · rw [mu, fe_st4 _ _ (by omega), b1, b2, b3, b8, a1, a2, a3, a8, a9]
    simp only [val4, val5, fe, extr_toNat]
    exact shift_arith _ _ _ _ _ (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
  · rw [mu, mb]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [ku.gpr r (by simp), kb.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1]),
      ka.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])]

/-! ## The reduction -/

theorem add4_mod (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    val4 (addCarry a0 b0 false) (addCarry a1 b1 (carryOut a0 b0 false))
        (addCarry a2 b2 (carryOut a1 b1 (carryOut a0 b0 false)))
        (addCarry a3 b3 (carryOut a2 b2 (carryOut a1 b1 (carryOut a0 b0 false)))) =
      (val4 a0 a1 a2 a3 + val4 b0 b1 b2 b3) % 2 ^ 256 := by
  have h := add4_value a0 a1 a2 a3 b0 b1 b2 b3 false
  dsimp only at h
  have hl := val4_lt (addCarry a0 b0 false) (addCarry a1 b1 (carryOut a0 b0 false))
    (addCarry a2 b2 (carryOut a1 b1 (carryOut a0 b0 false)))
    (addCarry a3 b3 (carryOut a2 b2 (carryOut a1 b1 (carryOut a0 b0 false))))
  rw [Bool.toNat_false, Nat.add_zero] at h
  omega

/-- The four words `reduce` stores. -/
def redW (w0 w1 w2 w3 w4 : Word) : Word × Word × Word × Word :=
  let q := redQ w3 w4
  let sg := (0 : Word) - (q >>> 63)
  let L := q * 19
  let H := mulHi q 19 - (sg &&& 19)
  let c0 := carryOut w0 L false
  let c1 := carryOut w1 H c0
  let c2 := carryOut w2 sg c1
  (addCarry w0 L false, addCarry w1 H c0, addCarry w2 sg c1, addCarry (w3 + (q <<< 63)) sg c2)

theorem redW_val (w0 w1 w2 w3 w4 : Word) :
    val4 (redW w0 w1 w2 w3 w4).1 (redW w0 w1 w2 w3 w4).2.1 (redW w0 w1 w2 w3 w4).2.2.1
      (redW w0 w1 w2 w3 w4).2.2.2 = redV w0 w1 w2 w3 w4 := by
  simp only [redW, redV]
  exact add4_mod _ _ _ _ _ _ _ _

/-- The words loaded, reduced and stored, given `x12 = 0` and `x13 = 19`. -/
theorem reduce_ok {s : State} {base : Addr} (hs : Scr s base large) {o t : Nat}
    (hz : s.gpr .x12 = 0) (h19 : s.gpr .x13 = 19)
    (ho : o % 8 = 0 ∧ o + 32 ≤ workSize large) (ht : t % 8 = 0 ∧ t + 40 ≤ workSize large) :
    WP isa (.block (reduce o t)) s fun u =>
      fe u.mem base o = redV (word s.mem base t) (word s.mem base (t + 8)) (word s.mem base (t + 16))
        (word s.mem base (t + 24)) (word s.mem base (t + 32)) ∧
      Outside base o 32 s.mem u.mem ∧
      KeepRegs [.x1, .x2, .x3, .x8, .x9, .x10, .x11, .x14, .x15] s u := by
  have _hcap := workSize_le large
  change WP isa (.block (([ld .x1 t, ld .x2 (t + 8), ld .x3 (t + 16), ld .x8 (t + 24),
    ld .x9 (t + 32)] : List Instr) ++ (([.extr .x .x10 .x9 .x8 63, .lsr .x .x11 .x9 63,
    .sub .x .x10 .x10 .x11, .lsl .x .x11 .x10 63, .add .x .x8 .x8 .x11,
    .lsr .x .x14 .x10 63, .sub .x .x14 .x12 .x14,
    .mul .x .x9 .x10 .x13, .umulh .x11 .x10 .x13, .logic .and .x .x15 .x14 .x13,
    .sub .x .x11 .x11 .x15,
    .adds .x .x1 .x1 .x9, .adcs .x .x2 .x2 .x11, .adcs .x .x3 .x3 .x14, .adc .x .x8 .x8 .x14] :
      List Instr) ++
    ([st .x1 o, st .x2 (o + 8), st .x3 (o + 16), st .x8 (o + 24)] : List Instr)))) s _
  rw [WP.block_append_iff]
  refine WP.mono (ld5_ok hs ht) fun a ⟨a1, a2, a3, a8, a9, ka⟩ => ?_
  have az : a.gpr .x12 = 0 := (ka.gpr _ (by decide)).trans hz
  have a19 : a.gpr .x13 = 19 := (ka.gpr _ (by decide)).trans h19
  rw [WP.block_append_iff]
  have hx : WP isa (.block ([.extr .x .x10 .x9 .x8 63, .lsr .x .x11 .x9 63,
      .sub .x .x10 .x10 .x11, .lsl .x .x11 .x10 63, .add .x .x8 .x8 .x11,
      .lsr .x .x14 .x10 63, .sub .x .x14 .x12 .x14,
      .mul .x .x9 .x10 .x13, .umulh .x11 .x10 .x13, .logic .and .x .x15 .x14 .x13,
      .sub .x .x11 .x11 .x15,
      .adds .x .x1 .x1 .x9, .adcs .x .x2 .x2 .x11, .adcs .x .x3 .x3 .x14, .adc .x .x8 .x8 .x14] :
        List Instr)) a fun b =>
      b.gpr .x1 = (redW (a.gpr .x1) (a.gpr .x2) (a.gpr .x3) (a.gpr .x8) (a.gpr .x9)).1 ∧
      b.gpr .x2 = (redW (a.gpr .x1) (a.gpr .x2) (a.gpr .x3) (a.gpr .x8) (a.gpr .x9)).2.1 ∧
      b.gpr .x3 = (redW (a.gpr .x1) (a.gpr .x2) (a.gpr .x3) (a.gpr .x8) (a.gpr .x9)).2.2.1 ∧
      b.gpr .x8 = (redW (a.gpr .x1) (a.gpr .x2) (a.gpr .x3) (a.gpr .x8) (a.gpr .x9)).2.2.2 ∧
      Keeps [.x1, .x2, .x3, .x8, .x9, .x10, .x11, .x14, .x15] a b := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_extr_x _ _ _ _ (by decide : 63 < 64),
      exec_lsr (by decide : 63 < 64), exec_lsl (by decide : 63 < 64), exec_sub_x, exec_add_x,
      exec_mul_x, exec_umulh_x, exec_and_x, exec_adds_x, exec_adcs_x, exec_adc_x,
      Option.some.injEq, exists_eq_left']
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
      reduceCtorEq, ite_true, ite_false, BitVec.setWidth_eq, az, a19]
    refine ⟨?_, ?_, ?_, ?_, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
    any_goals (simp only [redW, redQ, addCarry, carryOut, mulHi, Size.bits]; done)
    any_goals (simp only [redW, redQ, addCarry, carryOut, mulHi, Size.bits]; rfl)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, RegUpd.gpr_addWithCarry, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2,
      ite_false]
  refine WP.mono hx fun b ⟨b1, b2, b3, b8, kb⟩ => ?_
  have hsb : Scr b base large := (hs.of_keeps ka (by decide)).of_keeps kb (by decide)
  refine WP.mono (st4w_ok hsb ho .x1 .x2 .x3 .x8) fun u ⟨mu, ku⟩ => ?_
  have mb : b.mem = s.mem := by rw [kb.mem, ka.mem]
  refine ⟨?_, ?_, ⟨fun r hr => ?_, by rw [ku.rd, kb.rd, ka.rd], by rw [ku.wr, kb.wr, ka.wr],
    by rw [ku.sp, kb.sp, ka.sp]⟩⟩
  · rw [mu, fe_st4 _ _ (by omega), b1, b2, b3, b8, redW_val, a1, a2, a3, a8, a9]
  · rw [mu, mb]; exact st4_outside _ _ (by omega) _ _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [ku.gpr r (by simp), kb.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
        hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      ka.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1])]

end VG.Proof.Ed25519.AArch64.Inv
