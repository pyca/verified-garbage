module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointProductFinish
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionWords
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeFold
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointCarry
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionFold
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionMath
import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeReduction
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
import VerifiedGarbage.Proof.Framework.Block

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (folded)

def pointFoldOutRegs : List Reg := [.x2,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x19]
abbrev pointFoldWordAt (s : State) (i : Nat) : Word := s.gpr (pointProductRegs.getD i .x2)
abbrev pointFoldOutAt (s : State) (i : Nat) : Word := s.gpr (pointFoldOutRegs.getD i .x2)
def pointFoldClob : List Reg := [.x0,.x1,.x2,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x19]

def pointFoldCode : List Instr := [
  .subs .x .x1 .x1 .x1,
  .extr .x .x10 .x20 .x19 9,
  .adcs .x .x2 .x2 .x10,
  .extr .x .x10 .x21 .x20 9,
  .adcs .x .x11 .x11 .x10,
  .extr .x .x10 .x22 .x21 9,
  .adcs .x .x12 .x12 .x10,
  .extr .x .x10 .x23 .x22 9,
  .adcs .x .x13 .x13 .x10,
  .extr .x .x10 .x24 .x23 9,
  .adcs .x .x14 .x14 .x10,
  .extr .x .x10 .x25 .x24 9,
  .adcs .x .x15 .x15 .x10,
  .extr .x .x10 .x0 .x25 9,
  .adcs .x .x16 .x16 .x10,
  .extr .x .x10 .x4 .x0 9,
  .adcs .x .x17 .x17 .x10,
  .subImm .x .x0 .x6 512,
  .logic .orr .x .x19 .x19 .x0,
  .lsr .x .x10 .x4 9,
  .adcs .x .x19 .x19 .x10]

theorem pointFold_eq : (VG.Impl.Mont.AArch64.P521Field.doubleFnBlocks.flatten.drop 220).take 21 =
    pointFoldCode := by decide

theorem point_fold_ok (s : State) (hz : s.gpr .x6=0) :
    WP isa (.block pointFoldCode) s fun t =>
      (∀i,i<9 → pointFoldOutAt t i=(folded (pointFoldWordAt s)).1.getD i 0) ∧
      t.c=(folded (pointFoldWordAt s)).2 ∧ t.gpr .x1=0 ∧ Keeps pointFoldClob s t := by
  apply WP.of_runBlock
  simp only [pointFoldCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,RegUpd.c_write,
    BitVec.setWidth_eq,show (9 : Nat)<64 from by decide,show (512 : Nat)<4096 from by decide,
    ite_true,ite_false,reduceCtorEq,hz,self_sub_carry,Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,point_self_sub _,⟨?_,by simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]⟩⟩
  · intro i hi
    have cases_i : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega_arith
    rcases cases_i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · rfl
  · dsimp only [pointFoldClob]
    reg_keeps

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (corrected)

def pointCorrectClob : List Reg := [.x0,.x2,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x19]

def pointCorrectCode : List Instr := [
  .sbcs .x .x2 .x2 .x6,
  .sbcs .x .x11 .x11 .x6,
  .sbcs .x .x12 .x12 .x6,
  .sbcs .x .x13 .x13 .x6,
  .sbcs .x .x14 .x14 .x6,
  .sbcs .x .x15 .x15 .x6,
  .sbcs .x .x16 .x16 .x6,
  .sbcs .x .x17 .x17 .x6,
  .sbc .x .x19 .x19 .x6,
  .movz .x .x0 511 0,
  .logic .and .x .x19 .x19 .x0]

theorem pointCorrect_eq : (VG.Impl.Mont.AArch64.P521Field.doubleFnBlocks.flatten.drop 241).take 11 =
    pointCorrectCode := by decide

theorem point_correct_ok (s : State) (hz : s.gpr .x6=0) :
    WP isa (.block pointCorrectCode) s fun t =>
      (∀i,i<9 → pointFoldOutAt t i=(corrected ((List.range 9).map (pointFoldOutAt s)) s.c).getD i 0) ∧
      t.gpr .x0=511 ∧ Keeps pointCorrectClob s t := by
  apply WP.of_runBlock
  simp only [pointCorrectCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,show (16*0 : Nat)<64 from by decide,
    ite_true,ite_false,reduceCtorEq,hz,Option.some.injEq,exists_eq_left']
  refine ⟨?_,by rfl,⟨?_,by simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]⟩⟩
  · intro i hi
    have cases_i : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega_arith
    rcases cases_i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · dsimp only [pointCorrectClob]
    reg_keeps

end VG.Proof.Mont.AArch64.P521Field

end

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps)
open VG.Proof.Mont.AArch64.P521Square
  (value inputValue folded fieldPrime addWords_length corrected_length corrected_value prime_value)

theorem point_fold_output_value (s : State) :
    value ((List.range 9).map (pointFoldOutAt s))=regsVal s pointFoldOutRegs := rfl

theorem point_product_input_value (s : State) :
    inputValue (pointFoldWordAt s)=regsVal s pointProductRegs := by
  have hm : (List.range 17).map (pointFoldWordAt s)=pointProductRegs.map s.gpr := rfl
  rw [inputValue,hm,value_map_gpr]

theorem point_reduce_ok {s : State} (hz : s.gpr .x6=0)
    (hu : regsVal s pointProductRegs<fieldPrime*fieldPrime) :
    WP isa (.block (pointFoldCode++pointCorrectCode)) s fun t =>
      regsVal t pointFoldOutRegs<fieldPrime ∧
      regsVal t pointFoldOutRegs=regsVal s pointProductRegs%fieldPrime ∧
      t.gpr .x1=0 ∧ t.gpr .x0=511 ∧ Keeps pointFoldClob s t := by
  rw [WP.block_append_iff]
  refine WP.mono (point_fold_ok s hz) fun u ⟨fold,carry,z1,kf⟩ => ?_
  have hlen : (folded (pointFoldWordAt s)).1.length=9 := addWords_length _ _ _ rfl
  have efold := range9_eq hlen fold
  have zu : u.gpr .x6=0 := (kf.gpr _ (by decide)).trans hz
  refine WP.mono (point_correct_ok u zu) fun t ⟨correct,mask,kc⟩ => ?_
  have ecorrect := range9_eq (corrected_length ((List.range 9).map (pointFoldOutAt u)) u.c rfl) correct
  rw [efold,carry] at ecorrect
  have hv := congrArg value ecorrect
  rw [point_fold_output_value,corrected_value (pointFoldWordAt s)
    (by rw [point_product_input_value]; exact hu),point_product_input_value] at hv
  have hpos : 0<fieldPrime := by dsimp only [fieldPrime]; rw [prime_value]; decide
  exact ⟨by rw [hv]; exact Nat.mod_lt _ hpos,hv,(kc.gpr .x1 (by decide)).trans z1,mask,kf.trans (kc.mono (by decide))⟩

end VG.Proof.Mont.AArch64.P521Field
