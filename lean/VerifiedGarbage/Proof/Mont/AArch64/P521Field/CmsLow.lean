module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsComplement
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionWords
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-! The first pass adds the low halves of nine times the complemented limbs. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (addWords)

def cmsLowIn : List Reg := [.x20,.x21,.x22,.x23,.x17,.x19,.x2,.x16]
def cmsLowOut : List Reg := [.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10]
def cmsLowClob : List Reg := [.x0,.x1,.x20,.x21,.x22,.x23,.x17,.x19,.x2,.x16,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10]

def cmsLowCode : List Instr := [
  .movz .x .x1 9 0,
  .movz .x .x0 0 0,
  .sub .x .x20 .x0 .x20,
  .subImm .x .x20 .x20 1,
  .mul .x .x0 .x1 .x20,
  .umulh .x20 .x1 .x20,
  .adds .x .x3 .x3 .x0,
  .movz .x .x0 0 0,
  .sub .x .x21 .x0 .x21,
  .subImm .x .x21 .x21 1,
  .mul .x .x0 .x1 .x21,
  .umulh .x21 .x1 .x21,
  .adcs .x .x4 .x4 .x0,
  .movz .x .x0 0 0,
  .sub .x .x22 .x0 .x22,
  .subImm .x .x22 .x22 1,
  .mul .x .x0 .x1 .x22,
  .umulh .x22 .x1 .x22,
  .adcs .x .x5 .x5 .x0,
  .movz .x .x0 0 0,
  .sub .x .x23 .x0 .x23,
  .subImm .x .x23 .x23 1,
  .mul .x .x0 .x1 .x23,
  .umulh .x23 .x1 .x23,
  .adcs .x .x6 .x6 .x0,
  .movz .x .x0 0 0,
  .sub .x .x17 .x0 .x17,
  .subImm .x .x17 .x17 1,
  .mul .x .x0 .x1 .x17,
  .umulh .x17 .x1 .x17,
  .adcs .x .x7 .x7 .x0,
  .movz .x .x0 0 0,
  .sub .x .x19 .x0 .x19,
  .subImm .x .x19 .x19 1,
  .mul .x .x0 .x1 .x19,
  .umulh .x19 .x1 .x19,
  .adcs .x .x8 .x8 .x0,
  .movz .x .x0 0 0,
  .sub .x .x2 .x0 .x2,
  .subImm .x .x2 .x2 1,
  .mul .x .x0 .x1 .x2,
  .umulh .x2 .x1 .x2,
  .adcs .x .x9 .x9 .x0,
  .movz .x .x0 0 0,
  .sub .x .x16 .x0 .x16,
  .subImm .x .x16 .x16 1,
  .mul .x .x0 .x1 .x16,
  .umulh .x16 .x1 .x16,
  .adcs .x .x10 .x10 .x0]

theorem cms_low_words (s : State) :
    WP isa (.block cmsLowCode) s fun t =>
      cmsLowOut.map t.gpr=(addWords (cmsLowOut.map s.gpr) ((cmsLowIn.map s.gpr).map fun x => 9 * (~~~x)) false).1 ∧
      t.c=(addWords (cmsLowOut.map s.gpr) ((cmsLowIn.map s.gpr).map fun x => 9 * (~~~x)) false).2 ∧
      cmsLowIn.map t.gpr=(cmsLowIn.map s.gpr).map (fun x => mulHi 9 (~~~x)) ∧
      t.gpr .x1=9 ∧ Keeps cmsLowClob s t := by
  apply WP.of_runBlock
  simp only [cmsLowCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,Nat.mul_zero,Nat.reduceLT,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_write,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,
    show BitVec.setWidth 64 (9 : BitVec 16) <<< 0=(9 : BitVec 64) from rfl,
    show BitVec.setWidth 64 (0 : BitVec 16) <<< 0=(0 : BitVec 64) from rfl,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,?_,True.intro,⟨?_,?_,?_,?_,?_⟩⟩
  · simp only [cmsLowOut,cmsLowIn,List.map_cons,List.map_nil,addWords,addCarry,carryOut,RegUpd.gpr_write,RegUpd.gpr_addWithCarry,
      BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,cms_complement,Size.bits]
    rfl
  · simp only [cmsLowOut,cmsLowIn,List.map_cons,List.map_nil,addWords,addCarry,carryOut,cms_complement]
    rfl
  · simp only [cmsLowIn,List.map_cons,List.map_nil,mulHi,RegUpd.gpr_write,RegUpd.gpr_addWithCarry,
      BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,cms_complement]
  · dsimp only [cmsLowClob]
    reg_keeps
  · simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry]
  · simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry]
  · simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry]
  · simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]

end VG.Proof.Mont.AArch64.P521Field
