module
public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Mat
public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Row
public import VerifiedGarbage.Proof.Divstep.BatchBasic
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
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! ### `Ed25519.AArch64.Inv.Conn`, which only this module used -/

section

/-! # The inversion's rows as integers

A row of the code (`row_ok`) for the matrix entries `m₁`, `m₂` as `mat`
leaves them (magnitudes and masks) is `m₁ X + m₂ Y` modulo `2³²⁰`: `X`, `Y`
signed for the rows of `f` and `g` (`rowF_int`), unsigned for those of `u`
and `v` (`rowU_int`). -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Inv

open VG VG.AArch64 VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64

theorem maskN_cases (w : Word) : (w.msb = true ∧ maskN w = BitVec.allOnes 64) ∨
    (w.msb = false ∧ maskN w = 0) := by
  unfold maskN; cases w.msb <;> simp

theorem flip4_eq (m : Mem) (base : Addr) (o : Nat) (w : Word) :
    flip4 m base o (maskN w) = flipN w (fe m base o) := by
  unfold flipN
  obtain l0 := (word m base o).isLt
  obtain l1 := (word m base (o + 8)).isLt
  obtain l2 := (word m base (o + 16)).isLt
  obtain l3 := (word m base (o + 24)).isLt
  rcases maskN_cases w with ⟨h, e⟩ | ⟨h, e⟩
  · simp only [flip4, e, h, ↓reduceIte, BitVec.xor_allOnes, val4, fe, BitVec.toNat_not]
    omega_using []
  · simp only [flip4, e, h, Bool.false_eq_true, ↓reduceIte, val4, fe, BitVec.toNat_xor,
      show (0 : Word).toNat = 0 from rfl, Nat.xor_zero]

theorem top_msb (m : Mem) (base : Addr) (o : Nat) (w : Word) :
    (word m base (o + 24) ^^^ maskN w).msb = decide (2 ^ 255 ≤ flipN w (fe m base o)) := by
  rw [← flip4_eq]
  obtain l0 := (word m base o ^^^ maskN w).isLt
  obtain l1 := (word m base (o + 8) ^^^ maskN w).isLt
  obtain l2 := (word m base (o + 16) ^^^ maskN w).isLt
  rw [BitVec.msb_eq_decide]
  simp only [flip4, val4]
  congr 1
  apply propext
  omega_using []

theorem corrV_true_eq (m : Mem) (base : Addr) (o : Nat) (w : Word) :
    (corrV true (word m base (o + 24) ^^^ maskN w) (absW w) (maskN w)).toNat =
      topN w (fe m base o) := by
  simp only [corrV, ↓reduceIte, mask_eq]
  unfold topN
  obtain hm : maskN (word m base (o + 24) ^^^ maskN w) =
      if 2 ^ 255 ≤ flipN w (fe m base o) then BitVec.allOnes 64 else 0 := by
    rw [maskN, top_msb]; simp only [decide_eq_true_eq]
  rw [hm]
  split
  · rw [BitVec.allOnes_and, absN_word]
  · rw [BitVec.toNat_and, show (0 : Word).toNat = 0 from rfl, Nat.zero_and]

theorem corrV_false_eq (x : Word) (w : Word) :
    (corrV false x (absW w) (maskN w)).toNat = negN w := by
  simp only [corrV, Bool.false_eq_true, ↓reduceIte]
  rw [BitVec.and_comm]
  exact negN_word w

theorem negN_le_absN (w : Word) : negN w ≤ absN w := by unfold negN; split <;> omega_using []

/-- The carry of two entries, below `2⁶⁴`. -/
theorem car_eq (a b : Word) (h : absN a + absN b < 2 ^ 64) :
    ((absW a &&& maskN a) + (absW b &&& maskN b)).toNat = negN a + negN b := by
  rw [BitVec.toNat_add, negN_word, negN_word]
  have := negN_le_absN a; have := negN_le_absN b
  exact Nat.mod_eq_of_lt (by omega_arith)

/-- A row of `f` and `g` as integers. -/
theorem rowF_int {a b : Word} {X Y W : Nat} (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256)
    (h : (W + 2 ^ 256 * (topN a X + topN b Y)) % (2 ^ 256 * 2 ^ 64) =
      (negN a + negN b + flipN a X * absN a + flipN b Y * absN b) % (2 ^ 256 * 2 ^ 64)) :
    (W : Int) % 2 ^ 320 = (a.toInt * sv X + b.toInt * sv Y) % 2 ^ 320 := by
  obtain e1 := fterm a hX
  obtain e2 := fterm b hY
  rw [Nat.mul_comm (absN a) (flipN a X)] at e1
  rw [Nat.mul_comm (absN b) (flipN b Y)] at e2
  generalize flipN a X * absN a = P1 at e1 h
  generalize flipN b Y * absN b = P2 at e2 h
  rw [show (2 : Int) ^ 320 = 2 ^ 256 * 2 ^ 64 by rw [← pow_add]]
  omega_using [e1, e2, h]

/-- A row of `u` and `v` as integers. -/
theorem rowU_int {a b : Word} {X Y W : Nat} (hX : X < 2 ^ 256) (hY : Y < 2 ^ 256)
    (h : (W + 2 ^ 256 * (negN a + negN b)) % (2 ^ 256 * 2 ^ 64) =
      (negN a + negN b + flipN a X * absN a + flipN b Y * absN b) % (2 ^ 256 * 2 ^ 64)) :
    (W : Int) % 2 ^ 320 = (a.toInt * X + b.toInt * Y) % 2 ^ 320 := by
  obtain e1 := uterm a hX
  obtain e2 := uterm b hY
  rw [Nat.mul_comm (absN a) (flipN a X)] at e1
  rw [Nat.mul_comm (absN b) (flipN b Y)] at e2
  generalize flipN a X * absN a = P1 at e1 h
  generalize flipN b Y * absN b = P2 at e2 h
  rw [show (2 : Int) ^ 320 = 2 ^ 256 * 2 ^ 64 by rw [← pow_add]]
  omega_using [e1, e2, h]

end VG.Proof.Ed25519.AArch64.Inv

end

end

/-! ### `Ed25519.AArch64.Inv.Out`, which only this module used -/

section

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
  omega_using [h0, h1, h2]

/-- The five words at `t` into `x1`–`x3`, `x8`, `x9`. -/
theorem ld5_ok {s : State} {base : Addr} (hs : Scr s base large) {t : Nat}
    (ht : t % 8 = 0 ∧ t + 40 ≤ workSize large) :
    WP isa (.block [ld .x1 t, ld .x2 (t + 8), ld .x3 (t + 16), ld .x8 (t + 24), ld .x9 (t + 32)]) s
      fun u => u.gpr .x1 = word s.mem base t ∧ u.gpr .x2 = word s.mem base (t + 8) ∧
        u.gpr .x3 = word s.mem base (t + 16) ∧ u.gpr .x8 = word s.mem base (t + 24) ∧
        u.gpr .x9 = word s.mem base (t + 32) ∧ Keeps [.x1, .x2, .x3, .x8, .x9] s u := by
  obtain w1 : Reg.x1 ≠ .x0 := by decide
  obtain w2 : Reg.x2 ≠ .x0 := by decide
  obtain w3 : Reg.x3 ≠ .x0 := by decide
  obtain w8 : Reg.x8 ≠ .x0 := by decide
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    load_sc hs ht.1 (by omega_using [ht]), load_sc (hs.write w1 _) (d := t + 8) (by omega_using [ht]) (by omega_using [ht]),
    load_sc ((hs.write w1 _).write w2 _) (d := t + 16) (by omega_using [ht]) (by omega_using [ht]),
    load_sc (((hs.write w1 _).write w2 _).write w3 _) (d := t + 24) (by omega_using [ht]) (by omega_using [ht]),
    load_sc ((((hs.write w1 _).write w2 _).write w3 _).write w8 _) (d := t + 32) (by omega_using [ht])
      (by omega_using [ht]), Option.some.injEq, exists_eq_left']
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
  simp only [runBlock_cons, runStep_some, runBlock_nil, store_sc hs ho.1 (by omega_using [ho]),
    store_sc (hs.setMem _) (d := o + 8) (by omega_using [ho]) (by omega_using [ho]),
    store_sc ((hs.setMem _).setMem _) (d := o + 16) (by omega_using [ho]) (by omega_using [ho]),
    store_sc (((hs.setMem _).setMem _).setMem _) (d := o + 24) (by omega_using [ho]) (by omega_using [ho]),
    Option.some.injEq, exists_eq_left']
  exact ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl⟩

/-- The words loaded, shifted and stored. -/
theorem shift_ok {s : State} {base : Addr} (hs : Scr s base large) {o t : Nat}
    (ho : o % 8 = 0 ∧ o + 32 ≤ workSize large) (ht : t % 8 = 0 ∧ t + 40 ≤ workSize large) :
    WP isa (.block (shift o t)) s fun u =>
      fe u.mem base o = val5 s.mem base t / 2 ^ 59 % 2 ^ 256 ∧ Outside base o 32 s.mem u.mem ∧
      KeepRegs [.x1, .x2, .x3, .x8, .x9] s u := by
  obtain _hcap := workSize_le large
  change WP isa (.block (([ld .x1 t, ld .x2 (t + 8), ld .x3 (t + 16), ld .x8 (t + 24),
    ld .x9 (t + 32)] : List Instr) ++ (([.extr .x .x1 .x2 .x1 59, .extr .x .x2 .x3 .x2 59,
    .extr .x .x3 .x8 .x3 59, .extr .x .x8 .x9 .x8 59] : List Instr) ++
    ([st .x1 o, st .x2 (o + 8), st .x3 (o + 16), st .x8 (o + 24)] : List Instr)))) s _
  rw [WP.block_append_iff]
  refine WP.mono (ld5_ok hs ht) fun a ⟨a1, a2, a3, a8, a9, ka⟩ => ?_
  rw [WP.block_append_iff]
  obtain hx : WP isa (.block ([.extr .x .x1 .x2 .x1 59, .extr .x .x2 .x3 .x2 59,
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
  obtain hsb : Scr b base large := (hs.of_keeps ka (by decide)).of_keeps kb (by decide)
  refine WP.mono (st4w_ok hsb ho .x1 .x2 .x3 .x8) fun u ⟨mu, ku⟩ => ?_
  obtain mb : b.mem = s.mem := by rw [kb.mem, ka.mem]
  refine ⟨?_, ?_, ⟨fun r hr => ?_, by rw [ku.rd, kb.rd, ka.rd], by rw [ku.wr, kb.wr, ka.wr],
    by rw [ku.sp, kb.sp, ka.sp]⟩⟩
  · rw [mu, fe_st4 _ _ (by omega_using [ho, _hcap]), b1, b2, b3, b8, a1, a2, a3, a8, a9]
    simp only [val4, val5, fe, extr_toNat]
    exact shift_arith _ _ _ _ _ (BitVec.isLt _) (BitVec.isLt _) (BitVec.isLt _)
  · rw [mu, mb]; exact st4_outside _ _ (by omega_using [ho, _hcap]) _ _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [ku.gpr r (by simp), kb.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1]),
      ka.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])]

/-! ## The reduction -/

theorem add4_mod (a0 a1 a2 a3 b0 b1 b2 b3 : Word) :
    val4 (addCarry a0 b0 false) (addCarry a1 b1 (carryOut a0 b0 false))
        (addCarry a2 b2 (carryOut a1 b1 (carryOut a0 b0 false)))
        (addCarry a3 b3 (carryOut a2 b2 (carryOut a1 b1 (carryOut a0 b0 false)))) =
      (val4 a0 a1 a2 a3 + val4 b0 b1 b2 b3) % 2 ^ 256 := by
  obtain h := add4_value a0 a1 a2 a3 b0 b1 b2 b3 false
  dsimp only at h
  obtain hl := val4_lt (addCarry a0 b0 false) (addCarry a1 b1 (carryOut a0 b0 false))
    (addCarry a2 b2 (carryOut a1 b1 (carryOut a0 b0 false)))
    (addCarry a3 b3 (carryOut a2 b2 (carryOut a1 b1 (carryOut a0 b0 false))))
  rw [Bool.toNat_false, Nat.add_zero] at h
  omega_using [h, hl]

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
  obtain _hcap := workSize_le large
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
  obtain az : a.gpr .x12 = 0 := (ka.gpr _ (by decide)).trans hz
  obtain a19 : a.gpr .x13 = 19 := (ka.gpr _ (by decide)).trans h19
  rw [WP.block_append_iff]
  obtain hx : WP isa (.block ([.extr .x .x10 .x9 .x8 63, .lsr .x .x11 .x9 63,
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
  obtain hsb : Scr b base large := (hs.of_keeps ka (by decide)).of_keeps kb (by decide)
  refine WP.mono (st4w_ok hsb ho .x1 .x2 .x3 .x8) fun u ⟨mu, ku⟩ => ?_
  obtain mb : b.mem = s.mem := by rw [kb.mem, ka.mem]
  refine ⟨?_, ?_, ⟨fun r hr => ?_, by rw [ku.rd, kb.rd, ka.rd], by rw [ku.wr, kb.wr, ka.wr],
    by rw [ku.sp, kb.sp, ka.sp]⟩⟩
  · rw [mu, fe_st4 _ _ (by omega_using [ho, _hcap]), b1, b2, b3, b8, redW_val, a1, a2, a3, a8, a9]
  · rw [mu, mb]; exact st4_outside _ _ (by omega_using [ho, _hcap]) _ _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [ku.gpr r (by simp), kb.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
        hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      ka.gpr r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1])]

end VG.Proof.Ed25519.AArch64.Inv

end

end


/-! # A batch of the inversion modulo `p` on AArch64

What a batch's proof (`DivstepSound.batch_ok`) is built from: its rows are the
matrix's combinations (`row_ok`, `rowF_rel`, `rowU_rel`), shifted and reduced
(`outs_ok`: `shift_ok`, `reduce_ok`), and it counts down. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Inv

open VG VG.AArch64 VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64 VG.Spec.X25519
open VG.Proof.Mont.AArch64 (KeepRegs Keeps.regs)
open VG.Proof.Divstep (MSt msteps)
open VG.Proof.X25519.AArch64 (exec_movz)
open VG.Impl.Ed25519.AArch64 (ld st)
open VG.Impl.Ed25519.AArch64.Divstep (F G U V TF TG TU TV DSAVE batch shift reduce)

variable {large : Bool}

/-- The registers a batch may change. -/
abbrev batchRegs : List Reg :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x20]

/-- The low word of a field element, as an integer modulo `2⁶⁴`. -/
theorem low_rel {m : Mem} {base : Addr} {o : Nat} {f : Int} (h : sv (fe m base o) = f) :
    ((word m base o).toNat : Int) % 2 ^ 64 = f % 2 ^ 64 := by
  rw [← h]
  have := (word m base o).isLt
  have := (word m base (o + 8)).isLt
  have := (word m base (o + 16)).isLt
  have := (word m base (o + 24)).isLt
  unfold sv
  simp only [fe, val4]
  split <;> omega_arith

theorem lds3_ok {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa (.block [ld .x1 DSAVE, ld .x2 F, ld .x3 G]) s fun t =>
      t.gpr .x1 = word s.mem base DSAVE ∧ t.gpr .x2 = word s.mem base F ∧
      t.gpr .x3 = word s.mem base G ∧ Keeps [.x1, .x2, .x3] s t := by
  obtain _hmin := workSize_ge large
  change WP isa (.block (([ld .x1 DSAVE] : List Instr) ++ (([ld .x2 F] : List Instr) ++
    ([ld .x3 G] : List Instr)))) s _
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs (by decide) (by simp only [DSAVE]; omega_arith) .x1) fun a ⟨a1, ka⟩ => ?_
  obtain hsa := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hsa (by decide) (by simp only [F]; omega_arith) .x2) fun b ⟨b2, kb⟩ => ?_
  obtain hsb := hsa.of_keeps kb (by decide)
  refine WP.mono (ld_ok hsb (by decide) (by simp only [G]; omega_arith) .x3) fun t ⟨t3, kt⟩ => ?_
  refine ⟨by rw [kt.gpr _ (by decide), kb.gpr _ (by decide), a1],
    by rw [kt.gpr _ (by decide), b2, ka.mem], by rw [t3, kb.mem, ka.mem], ?_⟩
  exact (ka.mono (by decide)).trans ((kb.mono (by decide)).trans (kt.mono (by decide)))

/-- The registers after `mat`, for the matrix `T`. -/
structure MatRegs (T : MSt) (t : State) : Prop where
  z : t.gpr .x12 = 0
  u : t.gpr .x4 = absW (BitVec.ofInt 64 T.u)
  su : t.gpr .x14 = maskN (BitVec.ofInt 64 T.u)
  v : t.gpr .x5 = absW (BitVec.ofInt 64 T.v)
  sv' : t.gpr .x15 = maskN (BitVec.ofInt 64 T.v)
  q : t.gpr .x6 = absW (BitVec.ofInt 64 T.q)
  sq : t.gpr .x16 = maskN (BitVec.ofInt 64 T.q)
  r : t.gpr .x7 = absW (BitVec.ofInt 64 T.r)
  sr : t.gpr .x17 = maskN (BitVec.ofInt 64 T.r)
  c0 : t.gpr .x13 = (absW (BitVec.ofInt 64 T.u) &&& maskN (BitVec.ofInt 64 T.u)) +
    (absW (BitVec.ofInt 64 T.v) &&& maskN (BitVec.ofInt 64 T.v))
  c1 : t.gpr .x11 = (absW (BitVec.ofInt 64 T.q) &&& maskN (BitVec.ofInt 64 T.q)) +
    (absW (BitVec.ofInt 64 T.r) &&& maskN (BitVec.ofInt 64 T.r))

theorem MatRegs.keep {T : MSt} {t t' : State} (h : MatRegs T t)
    (k : KeepRegs [.x1, .x2, .x3, .x8, .x9, .x10] t t') : MatRegs T t' :=
  ⟨(k.gpr _ (by decide)).trans h.z, (k.gpr _ (by decide)).trans h.u, (k.gpr _ (by decide)).trans h.su,
    (k.gpr _ (by decide)).trans h.v, (k.gpr _ (by decide)).trans h.sv',
    (k.gpr _ (by decide)).trans h.q, (k.gpr _ (by decide)).trans h.sq,
    (k.gpr _ (by decide)).trans h.r, (k.gpr _ (by decide)).trans h.sr,
    (k.gpr _ (by decide)).trans h.c0, (k.gpr _ (by decide)).trans h.c1⟩

theorem absW_le {u : Int} (h : |u| ≤ 2 ^ 59) : (absW (BitVec.ofInt 64 u)).toNat ≤ 2 ^ 62 := by
  rw [absN_word]
  unfold absN
  rw [VG.Proof.Divstep.toInt_small h]
  rw [Int.abs_eq_natAbs] at h
  omega_arith

theorem absN_le {u : Int} (h : |u| ≤ 2 ^ 59) : absN (BitVec.ofInt 64 u) ≤ 2 ^ 59 := by
  unfold absN
  rw [VG.Proof.Divstep.toInt_small h]
  rw [Int.abs_eq_natAbs] at h
  omega_arith

/-- A row of `f` and `g` as the code leaves it, as integers. -/
theorem rowF_rel {m m' : Mem} {base : Addr} {t xo yo : Nat} {a b : Int}
    (ha : |a| ≤ 2 ^ 59) (hb : |b| ≤ 2 ^ 59)
    (h : (val5 m' base t + 2 ^ 256 *
          ((corrV true (word m base (xo + 24) ^^^ maskN (BitVec.ofInt 64 a)) (absW (BitVec.ofInt 64 a))
              (maskN (BitVec.ofInt 64 a))).toNat +
            (corrV true (word m base (yo + 24) ^^^ maskN (BitVec.ofInt 64 b)) (absW (BitVec.ofInt 64 b))
              (maskN (BitVec.ofInt 64 b))).toNat)) % (2 ^ 256 * 2 ^ 64) =
        (((absW (BitVec.ofInt 64 a) &&& maskN (BitVec.ofInt 64 a)) +
            (absW (BitVec.ofInt 64 b) &&& maskN (BitVec.ofInt 64 b))).toNat +
          flip4 m base xo (maskN (BitVec.ofInt 64 a)) * (absW (BitVec.ofInt 64 a)).toNat +
          flip4 m base yo (maskN (BitVec.ofInt 64 b)) * (absW (BitVec.ofInt 64 b)).toNat) % (2 ^ 256 * 2 ^ 64)) :
    (val5 m' base t : Int) % 2 ^ 320 = (a * sv (fe m base xo) + b * sv (fe m base yo)) % 2 ^ 320 := by
  rw [corrV_true_eq, corrV_true_eq, car_eq _ _ (by have := absN_le ha; have := absN_le hb; omega_arith),
    flip4_eq, flip4_eq, absN_word, absN_word] at h
  obtain e := rowF_int (val4_lt _ _ _ _) (val4_lt _ _ _ _) h
  rwa [VG.Proof.Divstep.toInt_small ha, VG.Proof.Divstep.toInt_small hb] at e

/-- A row of `u` and `v` as the code leaves it, as integers. -/
theorem rowU_rel {m m' : Mem} {base : Addr} {t xo yo : Nat} {a b : Int}
    (ha : |a| ≤ 2 ^ 59) (hb : |b| ≤ 2 ^ 59)
    (h : (val5 m' base t + 2 ^ 256 *
          ((corrV false (word m base (xo + 24) ^^^ maskN (BitVec.ofInt 64 a)) (absW (BitVec.ofInt 64 a))
              (maskN (BitVec.ofInt 64 a))).toNat +
            (corrV false (word m base (yo + 24) ^^^ maskN (BitVec.ofInt 64 b)) (absW (BitVec.ofInt 64 b))
              (maskN (BitVec.ofInt 64 b))).toNat)) % (2 ^ 256 * 2 ^ 64) =
        (((absW (BitVec.ofInt 64 a) &&& maskN (BitVec.ofInt 64 a)) +
            (absW (BitVec.ofInt 64 b) &&& maskN (BitVec.ofInt 64 b))).toNat +
          flip4 m base xo (maskN (BitVec.ofInt 64 a)) * (absW (BitVec.ofInt 64 a)).toNat +
          flip4 m base yo (maskN (BitVec.ofInt 64 b)) * (absW (BitVec.ofInt 64 b)).toNat) % (2 ^ 256 * 2 ^ 64)) :
    (val5 m' base t : Int) % 2 ^ 320 = (a * fe m base xo + b * fe m base yo) % 2 ^ 320 := by
  rw [corrV_false_eq, corrV_false_eq, car_eq _ _ (by have := absN_le ha; have := absN_le hb; omega_arith),
    flip4_eq, flip4_eq, absN_word, absN_word] at h
  obtain e := rowU_int (val4_lt _ _ _ _) (val4_lt _ _ _ _) h
  rwa [VG.Proof.Divstep.toInt_small ha, VG.Proof.Divstep.toInt_small hb] at e

theorem prod_bnd {a : Int} {U : Nat} (ha : |a| ≤ 2 ^ 59) (hU : U < 2 ^ 256) :
    -(2 ^ 59 * 2 ^ 256) ≤ a * U ∧ a * U ≤ 2 ^ 59 * 2 ^ 256 := by
  obtain h0 : (0 : Int) ≤ U := by positivity
  obtain h1 : (U : Int) ≤ 2 ^ 256 := by exact_mod_cast hU.le
  rw [abs_le] at ha
  obtain p1 := mul_nonneg (by linarith : (0 : Int) ≤ a + 2 ^ 59) h0
  obtain p2 := mul_nonneg (by linarith : (0 : Int) ≤ 2 ^ 59 - a) h0
  rw [add_mul] at p1
  rw [sub_mul] at p2
  constructor <;> linarith

theorem sum_bnd {a b : Int} {U V : Nat} (ha : |a| ≤ 2 ^ 59) (hb : |b| ≤ 2 ^ 59) (hU : U < 2 ^ 256)
    (hV : V < 2 ^ 256) : -2 ^ 317 ≤ a * U + b * V ∧ a * U + b * V < 2 ^ 317 := by
  obtain h1 := prod_bnd ha hU
  obtain h2 := prod_bnd hb hV
  obtain hK : (0 : Int) < 2 ^ 59 * 2 ^ 256 := by positivity
  rw [show (2 : Int) ^ 317 = 2 ^ 59 * 2 ^ 256 * 2 ^ 2 by rw [← pow_add, ← pow_add]]
  generalize (2 : Int) ^ 59 * 2 ^ 256 = K at h1 h2 hK ⊢
  constructor <;> linarith

theorem val5_out {base : Addr} {o n t : Nat} {m m' : Mem} (h : Outside base o n m m')
    (ht : t + 40 ≤ o ∨ o + n ≤ t) (hl : t + 40 < 2 ^ 64) : val5 m' base t = val5 m base t := by
  simp only [val5]
  rw [h.fe (by omega_arith) (by omega_arith), h.word (by omega_arith) (by omega_arith)]

theorem cnt_val {i : Nat} (hi : i < 10) :
    BitVec.ofNat 64 (10 - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (10 - (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega_arith

theorem scr_of {rs : List Reg} {s s' : State} {base : Addr} (hs : Scr s base large)
    (h : KeepRegs rs s s') (hr : .x0 ∉ rs) : Scr s' base large :=
  ⟨(h.gpr _ hr).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

/-- The counter one down. -/
theorem cnt_ok (s : State) {i : Nat} (hi : i < 10) (hc : s.gpr .x20 = BitVec.ofNat 64 (10 - i)) :
    WP isa (.block [.subImm .x .x20 .x20 1]) s fun t =>
      t.gpr .x20 = BitVec.ofNat 64 (10 - (i + 1)) ∧ Keeps [.x20] s t :=
  WP.block_cons_iff.mpr ⟨_, exec_subImm_x (imm := 1) (by decide), WP.block_nil
    ⟨by
      rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
      simp only [State.read, hc]
      exact cnt_val hi,
      ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr),
        rfl, rfl, rfl, rfl⟩⟩⟩

/-- The five words at `t` reduced, as they were before bytes outside them changed. -/
theorem redV_out {base : Addr} {o n t : Nat} {m m' : Mem} (h : Outside base o n m m')
    (ht : t + 40 ≤ o ∨ o + n ≤ t) (hl : t + 40 < 2 ^ 64) :
    redV (word m' base t) (word m' base (t + 8)) (word m' base (t + 16)) (word m' base (t + 24))
        (word m' base (t + 32)) =
      redV (word m base t) (word m base (t + 8)) (word m base (t + 16)) (word m base (t + 24))
        (word m base (t + 32)) := by
  rw [h.word (by omega_arith) (by omega_arith), h.word (by omega_arith) (by omega_arith), h.word (by omega_arith) (by omega_arith),
    h.word (by omega_arith) (by omega_arith), h.word (by omega_arith) (by omega_arith)]

/-- Five words at `t` reduced. -/
abbrev red5 (m : Mem) (base : Addr) (t : Nat) : Nat :=
  redV (word m base t) (word m base (t + 8)) (word m base (t + 16)) (word m base (t + 24))
    (word m base (t + 32))

/-- The rows shifted and reduced, and the counter one down. -/
theorem outs_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x12 = 0) {i : Nat}
    (hi : i < 10) (hc : s.gpr .x20 = BitVec.ofNat 64 (10 - i)) :
    WP isa (.block (shift F TF ++ (shift G TG ++ (([.movz .x .x13 19 0] : List Instr) ++ (reduce U TU ++
        (reduce V TV ++ ([.subImm .x .x20 .x20 1] : List Instr))))))) s
      fun t =>
        fe t.mem base F = val5 s.mem base TF / 2 ^ 59 % 2 ^ 256 ∧
        fe t.mem base G = val5 s.mem base TG / 2 ^ 59 % 2 ^ 256 ∧
        fe t.mem base U = red5 s.mem base TU ∧ fe t.mem base V = red5 s.mem base TV ∧
        t.gpr .x20 = BitVec.ofNat 64 (10 - (i + 1)) ∧
        word t.mem base DSAVE = word s.mem base DSAVE ∧
        Outside base 192 296 s.mem t.mem ∧ KeepRegs batchRegs s t := by
  obtain _hmin := workSize_ge large
  obtain _hcap := workSize_le large
  rw [WP.block_append_iff]
  refine WP.mono (shift_ok hs (o := F) (t := TF) ⟨by decide, by simp only [F]; omega_arith⟩
    ⟨by decide, by simp only [TF]; omega_arith⟩) fun a ⟨a1, oa, ka⟩ => ?_
  obtain hsa := scr_of hs ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (shift_ok hsa (o := G) (t := TG) ⟨by decide, by simp only [G]; omega_arith⟩
    ⟨by decide, by simp only [TG]; omega_arith⟩) fun b ⟨b1, ob, kb⟩ => ?_
  obtain hsb := scr_of hsa kb (by decide)
  rw [WP.block_append_iff]
  obtain hm : WP isa (.block [.movz .x .x13 19 0]) b fun c => c.gpr .x13 = 19 ∧ Keeps [.x13] b c :=
    WP.block_cons_iff.mpr ⟨_, exec_movz, WP.block_nil ⟨(RegUpd.gpr_write_self _ _ _ _).trans (by decide),
      ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr),
        rfl, rfl, rfl, rfl⟩⟩⟩
  refine WP.mono hm fun c ⟨c13, kc⟩ => ?_
  obtain hsc := hsb.of_keeps kc (by decide)
  obtain zc : c.gpr .x12 = 0 := by
    rw [kc.gpr _ (by decide), kb.gpr _ (by decide), ka.gpr _ (by decide), hz]
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok hsc (o := U) (t := TU) zc c13 ⟨by decide, by simp only [U]; omega_arith⟩
    ⟨by decide, by simp only [TU]; omega_arith⟩) fun d ⟨d1, od, kd⟩ => ?_
  obtain hsd := scr_of hsc kd (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok hsd (o := V) (t := TV) ((kd.gpr _ (by decide)).trans zc)
    ((kd.gpr _ (by decide)).trans c13) ⟨by decide, by simp only [V]; omega_arith⟩
    ⟨by decide, by simp only [TV]; omega_arith⟩) fun e ⟨e1, oe, ke⟩ => ?_
  obtain hse := scr_of hsd ke (by decide)
  have mc : c.mem = b.mem := kc.mem
  obtain cnt : e.gpr .x20 = BitVec.ofNat 64 (10 - i) := by
    rw [ke.gpr _ (by decide), kd.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide),
      ka.gpr _ (by decide), hc]
  refine WP.mono (cnt_ok e hi cnt) fun t ⟨t20, kt⟩ => ?_
  obtain ot : Outside base 488 0 e.mem t.mem := by rw [kt.mem]; exact Outside.refl _ _ _ _
  refine ⟨?_, ?_, ?_, ?_, t20, ?_, ?_, ?_⟩
  · rw [ot.fe (by decide) (by decide), oe.fe (by decide) (by decide), od.fe (by decide) (by decide),
      mc, ob.fe (by decide) (by decide), a1]
  · rw [ot.fe (by decide) (by decide), oe.fe (by decide) (by decide), od.fe (by decide) (by decide),
      mc, b1, val5_out oa (by decide) (by decide)]
  · rw [ot.fe (by decide) (by decide), oe.fe (by decide) (by decide), d1, mc,
      redV_out ob (by decide) (by decide), redV_out oa (by decide) (by decide)]
  · rw [ot.fe (by decide) (by decide), e1, redV_out od (by decide) (by decide), mc,
      redV_out ob (by decide) (by decide), redV_out oa (by decide) (by decide)]
  · rw [ot.word (by decide) (by decide), oe.word (by decide) (by decide),
      od.word (by decide) (by decide), mc, ob.word (by decide) (by decide),
      oa.word (by decide) (by decide)]
  · exact ((((oa.mono (by decide) (by decide)).trans (ob.mono (by decide) (by decide))).trans
      (mc ▸ (od.mono (by decide) (by decide)))).trans (oe.mono (by decide) (by decide))).trans
      (ot.mono (by decide) (by decide))
  · exact ((((ka.mono (by decide)).trans (kb.mono (by decide))).trans
      (((Keeps.regs kc).mono (by decide)).trans (kd.mono (by decide)))).trans (ke.mono (by decide))).trans
      ((Keeps.regs kt).mono (by decide))

end VG.Proof.Ed25519.AArch64.Inv
