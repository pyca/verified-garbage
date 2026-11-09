module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsLowAll
public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.CmsAndWords
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc

/-! The high-product pass also collects the middle limbs for carry detection. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (addWords)

def cmsHighOut : List Reg := [.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11]
def cmsMiddleRegs : List Reg := [.x4,.x5,.x6,.x7,.x8,.x9,.x10]
def cmsHighClob : List Reg := [.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x15]

def cmsHighCode : List Instr := [
  .adds .x .x4 .x4 .x20,
  .adcs .x .x5 .x5 .x21,
  .logic .and .x .x15 .x4 .x5,
  .adcs .x .x6 .x6 .x22,
  .logic .and .x .x15 .x15 .x6,
  .adcs .x .x7 .x7 .x23,
  .logic .and .x .x15 .x15 .x7,
  .adcs .x .x8 .x8 .x17,
  .logic .and .x .x15 .x15 .x8,
  .adcs .x .x9 .x9 .x19,
  .logic .and .x .x15 .x15 .x9,
  .adcs .x .x10 .x10 .x2,
  .logic .and .x .x15 .x15 .x10,
  .adc .x .x11 .x11 .x16]

theorem cms_high_words (s : State) :
    WP isa (.block cmsHighCode) s fun t =>
      cmsHighOut.map t.gpr=(addWords (cmsHighOut.map s.gpr) (cmsLowIn.map s.gpr) false).1 ∧
      t.gpr .x15=cmsAndWords (cmsMiddleRegs.map t.gpr) ∧ Keeps cmsHighClob s t := by
  apply WP.of_runBlock
  simp only [cmsHighCode,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_write,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,⟨?_,?_,?_,?_,?_⟩⟩
  · simp only [cmsHighOut,cmsLowIn,List.map_cons,List.map_nil,addWords,addCarry,carryOut,
      RegUpd.gpr_write,RegUpd.gpr_addWithCarry,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,Size.bits]
    rfl
  · simp only [cmsMiddleRegs,List.map_cons,List.map_nil,cmsAndWords,RegUpd.gpr_write,
      RegUpd.gpr_addWithCarry,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,BitVec.and_allOnes,BitVec.and_assoc]
  · dsimp only [cmsHighClob]
    reg_keeps
  · simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry]
  · simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry]
  · simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry]
  · simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]

end VG.Proof.Mont.AArch64.P521Field
