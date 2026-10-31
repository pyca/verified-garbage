module
public import VerifiedGarbage.Impl.Ed448.X86_64.WindowRegister
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.X86_64.Basic

import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-! Select one coordinate in registers, storing it only after scanning the table. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Window

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Impl.Ed448.X86_64.Window
open VG.Proof.X448.X86_64
open VG.Impl.X448.X86_64 (W sc slot stores)

private theorem cmp_calc : ∀ d < 17, ∀ i < 17,
    ((BitVec.ofNat 64 d - (BitVec.ofNat 32 i).signExtend 64) == 0) = decide (d = i) := by
  decide +kernel

theorem compareDigit_ok {s : State} {d i : Nat} (hd : d < 17) (hi : i < 17)
    (hr : s.gpr .r15 = BitVec.ofNat 64 d) :
    WP isa (.block (compareDigit i)) s fun u =>
      u.zf = decide (d = i) ∧ Keeps [] s u := by
  apply WP.of_runBlock
  simp only [compareDigit, runBlock_cons, runStep_some, runBlock_nil, reduceExec, execAlu,
    readSrc, hr, RegUpd.zf_arithFlags, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  exact ⟨cmp_calc d hd i hi, fun _ _ => rfl, rfl, rfl, rfl⟩

theorem chooseMem_ok {s : State} {base : Addr} (hs : Scr s base) {a : Nat}
    (ha : a + 56 ≤ 8192) {sw : Bool} (hz : s.zf = sw) :
    WP isa (.block (chooseMem a)) s fun u =>
      rv u W = (if sw then fe s.mem base a else rv s W) ∧ Keeps W s u := by
  have hr : ∀ i < 7, InRegions (s.rd ++ s.wr) (off base (a + 8 * i)) 8 :=
    fun i hi => hs.read (by omega)
  apply WP.of_runBlock
  cases sw <;>
    simp only [chooseMem, W, List.range_succ, List.range_zero, List.nil_append,
      List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil, List.cons_append,
      runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc, execCmov, eval,
      RegUpd.zf_setReg, hz, ea_sc, hs.rdi, State.load64,
      hr 0 (by decide), hr 1 (by decide), hr 2 (by decide), hr 3 (by decide),
      hr 4 (by decide), hr 5 (by decide), hr 6 (by decide), RegUpd.gpr_setReg,
      RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
      Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
      reduceCtorEq, ite_true, ite_false]
  all_goals
    constructor
    · simp only [rv, fe, mv, VG.Proof.X448.X86_64.word, RegUpd.gpr_setReg,
        reduceCtorEq, ite_true, ite_false, Nat.mul_zero, Nat.add_zero,
        Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd]
    · refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1,
        hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2, ite_false]

theorem chooseConst_ok {s : State} (v : Spec.X448.Fe) {sw : Bool} (hz : s.zf = sw) :
    WP isa (.block (chooseConst v)) s fun u =>
      rv u W = (if sw then wv (words7 v.val) else rv s W) ∧ Keeps (.rax :: W) s u := by
  apply WP.of_runBlock
  cases sw <;>
    simp only [chooseConst, W, words7, List.range_succ, List.range_zero, List.nil_append,
      List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_right,
      List.flatMap_cons, List.flatMap_nil, List.cons_append,
      runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc, execCmov, eval,
      RegUpd.zf_setReg, hz, RegUpd.gpr_setReg,
      Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left',
      reduceCtorEq, ite_true, ite_false]
  all_goals
    constructor
    · simp only [rv, wv, RegUpd.gpr_setReg, reduceCtorEq, ite_true, ite_false]
    · refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
        hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2, ite_false]

end VG.Proof.Ed448.X86_64.Window
