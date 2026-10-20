module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionWords
public import VerifiedGarbage.Impl.Mont.AArch64.P521Square
public import VerifiedGarbage.Proof.Ed25519.AArch64.Step
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TacticTemplate
import VerifiedGarbage.Spec.Weierstrass

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Square
open VG VG.AArch64 VG.Impl.Mont.AArch64.P521Square
open VG.Proof.Ed25519.AArch64 VG.Proof.Ed25519.Word64

abbrev wordsAt (s : State) (i : Nat) : Word := s.gpr (uRegs.getD i .x11)
abbrev reduceClob : List Reg := [.x3,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x19,.x20,.x30]

theorem fold_ok (s : State) (hz : s.gpr .x30 = 0) :
    WP isa (.block foldCode) s fun t =>
      (∀ i < 9, wordsAt t i = (folded (wordsAt s)).1.getD i 0) ∧
      t.c = (folded (wordsAt s)).2 ∧ t.gpr .x30 = 0 ∧ Keeps reduceClob s t := by
  apply WP.of_runBlock
  simp only [foldCode, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry, RegUpd.c_write,
    BitVec.setWidth_eq, Size.bits, show (9 : Nat) < 64 by decide,
    show (1 : Nat) < 4096 by decide, ite_true, ite_false, reduceCtorEq, hz, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · intro i hi
    have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
    rcases cases_i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · rfl
  · rfl
  · reg_keeps

theorem correct_ok (s : State) (hz : s.gpr .x30 = 0) :
    WP isa (.block correctCode) s fun t =>
      (∀ i < 9, wordsAt t i = (corrected ((List.range 9).map (wordsAt s)) s.c).getD i 0) ∧
      Keeps reduceClob s t := by
  apply WP.of_runBlock
  simp only [correctCode, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, RegUpd.gpr_addWithCarry, RegUpd.c_addWithCarry,
    BitVec.setWidth_eq, Size.bits, show (16 * 0 : Nat) < 64 by decide, ite_true, ite_false, reduceCtorEq, hz,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨?_, by simp only [RegUpd.mem_write, RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write, RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write, RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write, RegUpd.sp_addWithCarry]⟩⟩
  · intro i hi
    have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
    rcases cases_i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · reg_keeps

theorem rotate_ok (s : State) :
    WP isa (.block rotateCode) s fun t =>
      (∀ i < 9, wordsAt t i = (rotated (wordsAt s)).getD i 0) ∧
      Keeps reduceClob s t := by
  apply WP.of_runBlock
  simp only [rotateCode, runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    RegUpd.gpr_write, BitVec.setWidth_eq, Size.bits,
    show (9 : Nat) < 64 by decide, show (55 : Nat) < 64 by decide,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨?_, by simp only [RegUpd.mem_write],
    by simp only [RegUpd.rd_write], by simp only [RegUpd.wr_write],
    by simp only [RegUpd.sp_write]⟩⟩
  · intro i hi
    have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
    rcases cases_i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · reg_keeps

end VG.Proof.Mont.AArch64.P521Square
