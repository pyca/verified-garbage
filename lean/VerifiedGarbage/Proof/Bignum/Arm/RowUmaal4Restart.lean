module

public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal4Body
import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal4Fusion
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! The first word overwrites incoming r3; the pair advance overwrites flags. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm

theorem stepNew_set3 (k : Nat) (s : State) (v : BitVec 32) :
    stepNew k (s.setReg .r3 v) = stepNew k s := by
  simp only [stepNew, inW, accW, reduceCtorEq, ↓reduceIte, State.setReg]
  congr 1
  funext r
  cases r <;> rfl

theorem rowBodyU_exec (s : State) (h0 : WordReadyU 0 s) (h4 : WordReadyU 4 s) :
    execBlock isa rowBodyU s = some
      (advState (stepNew 4 (stepNew 0 s)), wordTraceU 0 s ++ wordTraceU 4 s) := by
  let a := (stepNew 0 s).setReg .r5 (s.gpr .r5)
  have a4 : WordReadyU 4 a := (ready_set5 _ _ _).mpr ((ready_stepNew _ _ _).mpr h4)
  have e0 := rowFirstU_exec s h0.1 h0.2
  have e4 := rowStepU_exec (by decide : 4 < 4096) a a4.1 a4.2
  change execBlock isa (rowFirstU ++ (rowStepU 4 ++ rowAdvance2)) s = _
  rw [execBlock_append, e0]
  simp only [Option.bind_some]
  change (execBlock isa (rowStepU 4 ++ rowAdvance2) a).map _ = _
  rw [execBlock_append, e4, Option.bind_some, advState_exec]
  simp only [Option.map_some, List.append_nil, a, stepNew_set5]
  rfl

def RowRestart (s t : State) : Prop := NoFlags (s.setReg .r3 (t.gpr .r3)) t

theorem rowBodyU_restart {s n t : State} {tr : List Leak}
    (agree : RowRestart s n) (run : Exec isa (.block rowBodyU) s tr t) :
    Exec isa (.block rowBodyU) n tr t := by
  obtain ⟨hr0,hw0,hr4,hw4,rfl,rfl⟩ := rowBodyU_forward run
  have h0 : WordReadyU 0 n := (ready_noFlags 0 agree).mp ⟨hr0,hw0⟩
  have h4 : WordReadyU 4 n := (ready_noFlags 4 agree).mp ⟨hr4,hw4⟩
  have e := Exec.block_iff.mpr (rowBodyU_exec n h0 h4)
  have same : NoFlags (stepNew 4 (stepNew 0 s)) (stepNew 4 (stepNew 0 n)) := by
    have first := stepNew_noFlags 0 agree
    rw [stepNew_set3] at first
    exact stepNew_noFlags 4 first
  have output := advState_noFlags_eq same
  rw [← output] at e
  have g0 := congrFun agree.gpr .r0
  have g12 := congrFun agree.gpr .r12
  simp only [gpr_setReg, reduceCtorEq, ↓reduceIte] at g0 g12
  simpa only [wordTraceU, ← g0, ← g12] using e

theorem rowLoopU_restart {s n t : State} {tr : List Leak}
    (agree : RowRestart s n) (run : Exec isa (.loop (.block rowBodyU) .ne) s tr t) :
    Exec isa (.loop (.block rowBodyU) .ne) n tr t := by
  cases run with
  | loopExit first exit => exact .loopExit (rowBodyU_restart agree first) exit
  | loopNext first branch tail => exact .loopNext (rowBodyU_restart agree first) branch tail

end VG.Proof.Bignum.Arm
