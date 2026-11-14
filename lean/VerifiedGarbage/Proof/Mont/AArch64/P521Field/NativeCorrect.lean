module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.NativeFold
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Final conditional correction and the canonical 521-bit mask. -/

-- separate module: machine correction after the native Mersenne fold
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Ed25519.AArch64 VG.Proof.Mont.AArch64.P521Square

def nativeCorrect : List Instr := [
  .sbcs .x .x5 .x5 .x2,
  .sbcs .x .x6 .x6 .x2,
  .sbcs .x .x7 .x7 .x2,
  .sbcs .x .x8 .x8 .x2,
  .sbcs .x .x9 .x9 .x2,
  .sbcs .x .x10 .x10 .x2,
  .sbcs .x .x11 .x11 .x2,
  .sbcs .x .x12 .x12 .x2,
  .sbc .x .x13 .x13 .x2,
  .movz .x .x1 511 0,
  .logic .and .x .x13 .x13 .x1]

theorem nativeCorrect_eq : (mulFnBlocks.flatten.drop 399).take 11=nativeCorrect := by decide

theorem native_correct_ok (s : State) (hz : s.gpr .x2=0) :
    WP isa (.block nativeCorrect) s fun t =>
      (∀i,i<9 → foldOutAt t i=(corrected ((List.range 9).map (foldOutAt s)) s.c).getD i 0) ∧
      Keeps foldClob s t := by
  apply WP.of_runBlock
  simp only [nativeCorrect,runBlock_cons,runStep_some,runBlock_nil,reduceExec,read_x,Size.bits,
    RegUpd.gpr_write,RegUpd.gpr_addWithCarry,RegUpd.c_addWithCarry,
    BitVec.setWidth_eq,show (16*0 : Nat)<64 from by decide,
    ite_true,ite_false,reduceCtorEq,hz,Option.some.injEq,exists_eq_left']
  refine ⟨?_,⟨?_,by simp only [RegUpd.mem_write,RegUpd.mem_addWithCarry],
    by simp only [RegUpd.rd_write,RegUpd.rd_addWithCarry],
    by simp only [RegUpd.wr_write,RegUpd.wr_addWithCarry],
    by simp only [RegUpd.sp_write,RegUpd.sp_addWithCarry]⟩⟩
  · intro i hi
    have cases_i : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega_arith
    rcases cases_i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · dsimp only [foldClob]
    reg_keeps

end VG.Proof.Mont.AArch64.P521Field
