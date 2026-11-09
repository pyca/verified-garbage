module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointEntry
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Restore the fused doubler's workspace pointer and saved general registers. -/

-- separate module: the measured reverse-pair restoration schedule
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (lane)
open VG.Proof.Weierstrass.AArch64.Mont (exec_umov)

def doubleExit : List Instr := [
  .umov .x .x0 .v25 0,
  .umov .x .x27 .v20 0,
  .umov .x .x28 .v20 1,
  .umov .x .x25 .v19 0,
  .umov .x .x26 .v19 1,
  .umov .x .x23 .v18 0,
  .umov .x .x24 .v18 1,
  .umov .x .x21 .v17 0,
  .umov .x .x22 .v17 1,
  .umov .x .x19 .v16 0,
  .umov .x .x20 .v16 1]

theorem doubleExit_eq : ((doubleFnBlocks.drop 93).flatten.drop 14).take 11=doubleExit := by decide

theorem double_exit_ok (s : State) :
    WP isa (.block doubleExit) s fun t =>
      t.gpr .x0=(s.v .v25).extractLsb' 0 64 ∧
      (∀i (h : i<nativeSaved.length),t.gpr nativeSaved[i]=lane s.v i) ∧
      Keeps (.x0::nativeSaved) s t ∧ t.v=s.v := by
  apply WP.of_runBlock
  simp only [doubleExit,runBlock_cons,runStep_some,runBlock_nil,reduceExec,Size.bits,Nat.reduceMul,Nat.reduceLT,
    RegUpd.gpr_write,RegUpd.v_write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,⟨?_,by simp only [RegUpd.mem_write],by simp only [RegUpd.rd_write],
    by simp only [RegUpd.wr_write],by simp only [RegUpd.sp_write]⟩,
    trivial⟩
  · trivial
  · intro i hi
    have cases_i : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by
      have hlen : nativeSaved.length=10 := rfl
      omega_arith
    rcases cases_i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · dsimp only [nativeSaved]
    reg_keeps

end VG.Proof.Mont.AArch64.P521Field
