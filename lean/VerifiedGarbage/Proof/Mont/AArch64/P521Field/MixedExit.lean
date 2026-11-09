module

public import VerifiedGarbage.Proof.Mont.AArch64.P521Field.PointEntry
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.AArch64.Reduce
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! Restore the fused mixed adder's workspace pointer and saved general registers. -/

-- separate module: the measured reverse-pair restoration schedule
@[expose] public section
namespace VG.Proof.Mont.AArch64.P521Field
open VG VG.AArch64 VG.Impl.Mont.AArch64.P521Field
open VG.Proof.Ed25519.AArch64
open VG.Proof.Mont.AArch64.P521Square (lane)
open VG.Proof.Weierstrass.AArch64.Mont (exec_umov)

def mixedExit : List Instr := [
  .umov .x .x0 .v25 0,
  .umov .x .x30 .v24 0,
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

theorem mixedExit_eq : ((mixedFnBlocks.drop 138).flatten.drop 5).take 12=mixedExit := by decide

theorem mixed_exit_ok (s : State) :
    WP isa (.block mixedExit) s fun t =>
      t.gpr .x0=(s.v .v25).extractLsb' 0 64 ∧ t.gpr .x30=(s.v .v24).extractLsb' 0 64 ∧
      (∀i (h : i<nativeSaved.length),t.gpr nativeSaved[i]=lane s.v i) ∧
      Keeps (.x0::.x30::nativeSaved) s t ∧ t.v=s.v := by
  apply WP.of_runBlock
  simp only [mixedExit,runBlock_cons,runStep_some,runBlock_nil,reduceExec,Size.bits,Nat.reduceMul,Nat.reduceLT,
    RegUpd.gpr_write,RegUpd.v_write,BitVec.setWidth_eq,reduceCtorEq,ite_true,ite_false,
    Option.some.injEq,exists_eq_left']
  refine ⟨?_,?_,?_,⟨?_,by simp only [RegUpd.mem_write],by simp only [RegUpd.rd_write],
    by simp only [RegUpd.wr_write],by simp only [RegUpd.sp_write]⟩,
    trivial⟩
  · trivial
  · trivial
  · intro i hi
    have cases_i : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 := by
      have hlen : nativeSaved.length=10 := rfl
      omega_arith
    rcases cases_i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · dsimp only [nativeSaved]
    reg_keeps

/-- With the entry's save lanes intact, the emitted exit restores the caller. -/
theorem mixed_exit_restores (caller s : State)
    (workspace : (s.v .v25).extractLsb' 0 64=caller.gpr .x0)
    (link : (s.v .v24).extractLsb' 0 64=caller.gpr .x30)
    (saved : ∀i (h : i<nativeSaved.length),lane s.v i=caller.gpr nativeSaved[i]) :
    WP isa (.block mixedExit) s fun t =>
      t.gpr .x0=caller.gpr .x0 ∧ t.gpr .x30=caller.gpr .x30 ∧
      (∀r∈nativeSaved,t.gpr r=caller.gpr r) ∧
      Keeps (.x0::.x30::nativeSaved) s t ∧ t.v=s.v := by
  refine WP.mono (mixed_exit_ok s) fun t ⟨e0,e30,es,k,v⟩ =>
    ⟨e0.trans workspace,e30.trans link,?_,k,v⟩
  intro r hr
  obtain ⟨i,hi,he⟩ := List.getElem_of_mem hr
  subst r
  exact (es i hi).trans (saved i hi)

end VG.Proof.Mont.AArch64.P521Field
