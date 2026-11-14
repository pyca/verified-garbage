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
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionFold
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionMath
public import VerifiedGarbage.Proof.Mont.AArch64.Words
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
import VerifiedGarbage.Proof.Framework.Block

/-! ### `Mont.AArch64.P521Square.ReductionMachine`, which only this module used -/

section

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
    have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega_using [hi]
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
    have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega_using [hi]
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
    have cases_i : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega_using [hi]
    rcases cases_i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · reg_keeps

end VG.Proof.Mont.AArch64.P521Square

end

end


@[expose] public section
set_option exponentiation.threshold 1024
namespace VG.Proof.Mont.AArch64.P521Square
open VG VG.AArch64 VG.Impl.Mont.AArch64.P521Square
open VG.Proof.Ed25519.AArch64

abbrev outputWords (s : State) : List Word := (List.range 9).map (wordsAt s)

theorem output_eq {s : State} {xs : List Word} (hl : xs.length = 9)
    (h : ∀ i < 9, wordsAt s i = xs.getD i 0) : outputWords s = xs := by
  apply List.ext_getElem
  · simpa using hl.symm
  · intro i hi hi'
    have hi9 : i < 9 := by simpa using hi
    simpa only [outputWords, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some] using h i hi9

theorem corrected_length (xs : List Word) (c : Bool) (hl : xs.length = 9) :
    (corrected xs c).length = 9 := by
  have hr := addWords_length xs (List.replicate 9 (~~~(0 : Word))) c (by simpa using hl)
  simp only [corrected, List.length_append, List.length_take, List.length_singleton, hr, hl]
  rfl

theorem input_regs (s : State) : inputValue (wordsAt s) = regsVal s uRegs := rfl

theorem output_regs (s : State) : value (outputWords s) = regsVal s (uRegs.take 9) := rfl

/-- The fold and correction also give the ordinary field residue, before
the Montgomery representation's final cyclic rotation. -/
theorem canonical_reduction_ok (s : State) (hz : s.gpr .x30 = 0)
    (hu : regsVal s uRegs < fieldPrime*fieldPrime) :
    WP isa (.block (foldCode ++ correctCode)) s fun t =>
      regsVal t (uRegs.take 9) < fieldPrime ∧
      regsVal t (uRegs.take 9) = regsVal s uRegs % fieldPrime ∧
      Keeps reduceClob s t := by
  rw [WP.block_append_iff]
  refine WP.mono (fold_ok s hz) fun s₁ ⟨h₁,c₁,z₁,k₁⟩ => ?_
  have hl : (folded (wordsAt s)).1.length = 9 := addWords_length _ _ _ rfl
  have e₁ := output_eq hl h₁
  refine WP.mono (correct_ok s₁ z₁) fun t ⟨h₂,k₂⟩ => ?_
  have e₂ := output_eq (corrected_length (outputWords s₁) s₁.c rfl) h₂
  rw [e₁,c₁] at e₂
  have hv : value (outputWords t) = regsVal s uRegs % fieldPrime := by
    rw [e₂,corrected_value (wordsAt s) (by simpa only [input_regs] using hu),input_regs]
  rw [output_regs] at hv
  exact ⟨by rw [hv]; exact Nat.mod_lt _ (by decide),hv,k₁.trans k₂⟩

/-- Exact fold, conditional correction, and cyclic Montgomery rotation. -/
theorem reduction_ok (s : State) (hz : s.gpr .x30 = 0)
    (hu : regsVal s uRegs < fieldPrime*fieldPrime) :
    WP isa (.block (foldCode ++ correctCode ++ rotateCode)) s fun t =>
      regsVal t (uRegs.take 9) < fieldPrime ∧
      regsVal t (uRegs.take 9) * montBase % fieldPrime = regsVal s uRegs % fieldPrime ∧
      Keeps reduceClob s t := by
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (fold_ok s hz) fun s₁ ⟨h₁, c₁, z₁, k₁⟩ => ?_
  have hl : (folded (wordsAt s)).1.length = 9 := addWords_length _ _ _ rfl
  have e₁ := output_eq hl h₁
  rw [WP.block_append_iff]
  refine WP.mono (correct_ok s₁ z₁) fun s₂ ⟨h₂, k₂⟩ => ?_
  have e₂ := output_eq (corrected_length (outputWords s₁) s₁.c rfl) h₂
  rw [e₁, c₁] at e₂
  have hv : value (outputWords s₂) = regsVal s uRegs % fieldPrime := by
    rw [e₂, corrected_value (wordsAt s) (by simpa only [input_regs] using hu), input_regs]
  have hb : value (outputWords s₂) < fieldPrime := by
    rw [hv]
    exact Nat.mod_lt _ (by decide)
  refine WP.mono (rotate_ok s₂) fun t ⟨h₃, k₃⟩ => ?_
  have hlen : (rotated (wordsAt s₂)).length = 9 := rfl
  have e₃ := output_eq hlen h₃
  have hr := rotated_value (wordsAt s₂) (by change value (outputWords s₂) < _; exact Nat.lt_trans hb (by decide))
  have hm := rotation_mod hb
  rw [← hr, ← e₃, output_regs] at hm
  exact ⟨hm.1, hm.2.trans hv, k₁.trans (k₂.trans k₃)⟩

end VG.Proof.Mont.AArch64.P521Square
