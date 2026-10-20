module

public import VerifiedGarbage.Impl.Ed448.X86_64.Wnaf.Joint
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.X448.X86_64.Basic
import VerifiedGarbage.Proof.Ed448.X86_64.VerifyLoop
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.MlKem.X86_64.Wp
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Data.Nat.Totient
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual

/-! Decoding the signed byte digits used by public table selection. -/

@[expose] public section

namespace VG.Proof.Ed448.X86_64.Wnaf
open VG VG.X86_64 VG.Impl.Ed448.X86_64.Wnaf
open VG.Proof.X448.X86_64

abbrev CodeByte (d : Int) : Byte := (BitVec.ofInt 64 d).setWidth 8
abbrev DigitWord (d : Int) : BitVec 64 := (CodeByte d).setWidth 64

theorem bounded_index {d : Int} (h : -15 ≤ d ∧ d ≤ 15) : ∃ (i : Nat), i < 31 ∧ d = (i : Int) - 15 := by
  refine ⟨(d + 15).toNat, ?_, ?_⟩ <;> omega

private theorem digit_zero : ∀ (i : Nat), i < 31 →
    (DigitWord ((i : Int) - 15) &&& DigitWord ((i : Int) - 15) == 0) = decide ((i : Int) - 15 = 0) := by
  decide +kernel

private theorem magnitude_calc : ∀ (i : Nat), i < 31 →
    (if (!decide ((DigitWord ((i : Int) - 15)).toNat < ((128 : BitVec 32).signExtend 64).toNat)) = true
      then (256 : BitVec 32).setWidth 64 - DigitWord ((i : Int) - 15) else DigitWord ((i : Int) - 15)) =
      BitVec.ofNat 64 ((i : Int) - 15).natAbs := by decide +kernel

theorem getDigit_ok {s : State} {base : Addr} (hs : Scr s base) {o t : Nat} {d : Int}
    (ho : o + t + 1 ≤ 8192) (hd : -15 ≤ d ∧ d ≤ 15) (hr : s.gpr .rbx = BitVec.ofNat 64 t)
    (hm : s.mem (off base (o + t)) = CodeByte d) :
    WP isa (.block (getDigit o)) s fun u =>
      u.gpr .r15 = DigitWord d ∧ u.zf = some (decide (d = 0)) ∧ Keeps [.r15] s u := by
  obtain ⟨i, hi, rfl⟩ := bounded_index hd
  have hread := hs.read ho
  apply WP.of_runBlock
  simp only [getDigit, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    State.load8, ea_bitsAt hs.rdi hr, hread, hm, RegUpd.gpr_setReg_self, RegUpd.zf_arithFlags,
    RegUpd.gpr_arithFlags, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left', ite_true]
  refine ⟨trivial, digit_zero i hi, fun r h => ?_, rfl, rfl, rfl⟩
  have hn : r ≠ .r15 := by simpa only [List.mem_cons, List.not_mem_nil, or_false] using h
  simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg, hn, ite_false]

theorem magnitude_ok {s : State} {d : Int} (hd : -15 ≤ d ∧ d ≤ 15)
    (hr : s.gpr .r15 = DigitWord d) :
    WP isa (.block magnitude) s fun u =>
      u.gpr .r15 = BitVec.ofNat 64 d.natAbs ∧ Keeps [.rax, .r15] s u := by
  obtain ⟨i, hi, rfl⟩ := bounded_index hd
  xrun [magnitude, hr, execCmov, eval]
  simp only [apply_ite State.gpr, ite_apply, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    reduceCtorEq, ite_true, ite_false, hr]
  refine ⟨magnitude_calc i hi, fun r h => ?_, ?_, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
    simp only [apply_ite State.gpr, ite_apply, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
      h.1, h.2, ite_false, ite_self]
  · simp only [apply_ite State.mem, RegUpd.mem_setReg, RegUpd.mem_setFlags, ite_self]
  · simp only [apply_ite State.rd, RegUpd.rd_setReg, RegUpd.rd_setFlags, ite_self]
  · simp only [apply_ite State.wr, RegUpd.wr_setReg, RegUpd.wr_setFlags, ite_self]

end VG.Proof.Ed448.X86_64.Wnaf
