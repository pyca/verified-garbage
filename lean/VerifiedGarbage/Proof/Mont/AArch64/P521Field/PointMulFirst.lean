module

-- separate module: The first nine-limb zero-accumulator arithmetic replay costs 0.43s of proof versus 0.30s of imports; PointMulProduct composition reuses its checked carry/value equations.

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.MulFirst
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! First inline product row, with the measured carry-zero register. -/

@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Proof.Mont VG.Proof.Mont.AArch64
open VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (value)

def pointMulRow0Out : List Reg := [.x15,.x16,.x17,.x19,.x20,.x21,.x22,.x23,.x24,.x1]
def pointMulRow0Clob : List Reg := .x0::.x14::pointMulRow0Out
def pointMulRow0Arithmetic : List Instr := [
  .mul .x .x15 .x3 .x5,
  .umulh .x16 .x3 .x5,
  .mul .x .x14 .x3 .x6,
  .umulh .x17 .x3 .x6,
  .adds .x .x16 .x16 .x14,
  .mul .x .x14 .x3 .x7,
  .umulh .x19 .x3 .x7,
  .adcs .x .x17 .x17 .x14,
  .mul .x .x14 .x3 .x8,
  .umulh .x20 .x3 .x8,
  .adcs .x .x19 .x19 .x14,
  .mul .x .x14 .x3 .x9,
  .umulh .x21 .x3 .x9,
  .adcs .x .x20 .x20 .x14,
  .mul .x .x14 .x3 .x10,
  .umulh .x22 .x3 .x10,
  .adcs .x .x21 .x21 .x14,
  .mul .x .x14 .x3 .x11,
  .umulh .x23 .x3 .x11,
  .adcs .x .x22 .x22 .x14,
  .mul .x .x14 .x3 .x12,
  .umulh .x24 .x3 .x12,
  .adcs .x .x23 .x23 .x14,
  .mul .x .x14 .x3 .x13,
  .umulh .x1 .x3 .x13,
  .adcs .x .x24 .x24 .x14,
  .movz .x .x0 0 0,
  .adc .x .x1 .x1 .x0]

theorem pointMulRow0_arithmetic_words_zero (s : State) :
    WP isa (.block pointMulRow0Arithmetic) s fun t =>
      pointMulRow0Out.map t.gpr = firstRow (s.gpr .x3) (bRegs.map s.gpr) ∧
      t.gpr .x0=0 ∧ Keeps pointMulRow0Clob s t := by
  apply WP.of_runBlock
  simp only [pointMulRow0Arithmetic,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,RegUpd.c_write,
    BitVec.setWidth_eq,ite_true,ite_false,reduceCtorEq,Nat.reduceMul,Nat.reduceLT,Option.some.injEq,exists_eq_left']
  refine ⟨?_,rfl,⟨?_,by simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]⟩⟩
  · simp only [pointMulRow0Out,bRegs,List.map_cons,List.map_nil,firstRow,firstChain,
      addCarry,carryOut,mulHi,RegUpd.gpr_write,RegUpd.gpr_addWithCarry,
      BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false]
    rfl
  · dsimp only [pointMulRow0Clob,pointMulRow0Out]
    reg_keeps

theorem pointMulRow0_arithmetic_value_zero (s : State) :
    WP isa (.block pointMulRow0Arithmetic) s fun t =>
      regsVal t pointMulRow0Out = (s.gpr .x3).toNat*regsVal s bRegs ∧
      t.gpr .x0=0 ∧ Keeps pointMulRow0Clob s t := by
  refine WP.mono (pointMulRow0_arithmetic_words_zero s) fun t ⟨h,z,k⟩ => ?_
  have e := congrArg value h
  rw [value_map_gpr,firstRow_value,value_map_gpr] at e
  exact ⟨e,z,k⟩


end VG.Proof.Mont.AArch64.P521Field
