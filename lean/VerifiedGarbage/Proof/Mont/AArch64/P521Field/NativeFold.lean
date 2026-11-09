module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulLast
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionWords
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.Omega

/-! Fold the streamed product at bit 521 using its measured schedule. -/

-- separate module: first reduction carry chain before conditional correction
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont.AArch64
open VG.Impl.Mont.AArch64 VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519.Word64
open VG.Proof.Mont.AArch64.P521Square (folded)

def foldLowRegs : List Reg := [.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12]
def foldInputs : List Reg := foldLowRegs++row8In
abbrev foldWordAt (s : State) (i : Nat) : Word := s.gpr (foldInputs.getD i .x5)
abbrev foldOutAt (s : State) (i : Nat) : Word := s.gpr (bRegs.getD i .x5)
def foldClob : List Reg := [.x1,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14]
def nativeFold : List Instr := (mulFnBlocks.flatten.drop 370).take 29
def nativeFoldLoads : List Instr := loadsR .x27 foldLowRegs 0

def nativeFoldArith : List Instr := [
  .subs .x .x1 .x1 .x1,
  .extr .x .x14 .x25 .x24 9,
  .adcs .x .x5 .x5 .x14,
  .extr .x .x14 .x26 .x25 9,
  .adcs .x .x6 .x6 .x14,
  .extr .x .x14 .x15 .x26 9,
  .adcs .x .x7 .x7 .x14,
  .extr .x .x14 .x16 .x15 9,
  .adcs .x .x8 .x8 .x14,
  .extr .x .x14 .x17 .x16 9,
  .adcs .x .x9 .x9 .x14,
  .extr .x .x14 .x19 .x17 9,
  .adcs .x .x10 .x10 .x14,
  .extr .x .x14 .x20 .x19 9,
  .adcs .x .x11 .x11 .x14,
  .extr .x .x14 .x21 .x20 9,
  .adcs .x .x12 .x12 .x14,
  .subImm .x .x1 .x2 512,
  .logic .orr .x .x13 .x24 .x1,
  .lsr .x .x14 .x21 9,
  .adcs .x .x13 .x13 .x14]

theorem nativeFold_hoist : hoistLoads .x27 nativeFold=some (nativeFoldLoads,nativeFoldArith) := by decide

theorem self_sub_carry (x : Word) :
    decide (2^64≤x.toNat+(~~~x).toNat+true.toNat)=true := by
  simp only [BitVec.toNat_not,Bool.toNat_true,decide_eq_true_eq]
  have h := x.isLt
  omega_arith

theorem fold_arith_ok (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block nativeFoldArith) s fun t =>
      (∀i,i<9 → foldOutAt t i=(folded (foldWordAt s)).1.getD i 0) ∧
      t.c=(folded (foldWordAt s)).2 ∧ Keeps foldClob s t := by
  apply WP.of_runBlock
  simp only [nativeFoldArith,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,RegUpd.c_write,
    BitVec.setWidth_eq,show (9 : Nat)<64 from by decide,show (512 : Nat)<4096 from by decide,
    ite_true,ite_false,reduceCtorEq,hz,self_sub_carry,Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,⟨?_,by simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]⟩⟩
  · intro i hi
    have cases_i : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega_arith
    rcases cases_i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · rfl
  · dsimp only [foldClob]
    reg_keeps

end VG.Proof.Mont.AArch64.P521Field
