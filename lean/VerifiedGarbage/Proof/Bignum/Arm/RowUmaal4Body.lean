module

public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal4Pair
public import VerifiedGarbage.Proof.Bignum.Arm.RowUmaal4Step
import VerifiedGarbage.Proof.Framework.Arm.RegUpd
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Four sequential UMAAL words retain the old row's carry and last accumulator. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Arm.RegUpd VG.Impl.Bignum.Arm

def WordReadyU (k : Nat) (s : State) : Prop :=
  InRegions (s.rd ++ s.wr) (State.addr (s.gpr .r12 + BitVec.ofNat 32 k)) 4 ∧
  InRegions s.wr (State.addr (s.gpr .r0 + BitVec.ofNat 32 k)) 4

theorem ready_stepNew (k j : Nat) (s : State) : WordReadyU j (stepNew k s) ↔ WordReadyU j s := by
  rfl

theorem ready_set5 (j : Nat) (s : State) (v : BitVec 32) : WordReadyU j (s.setReg .r5 v) ↔ WordReadyU j s := by
  rfl

theorem rowBodyU4_exec (s : State) (h0 : WordReadyU 0 s) (h4 : WordReadyU 4 s)
    (h8 : WordReadyU 8 s) (h12 : WordReadyU 12 s) :
    execBlock isa rowBodyU4 s = some
      (advState4 (stepNew 12 (stepNew 8 (stepNew 4 (stepNew 0 s)))),
        wordTraceU 0 s ++ wordTraceU 4 s ++ wordTraceU 8 s ++ wordTraceU 12 s) := by
  let a := (stepNew 0 s).setReg .r5 (s.gpr .r5)
  let b := (stepNew 4 a).setReg .r5 (a.gpr .r5)
  let c := (stepNew 8 b).setReg .r5 (b.gpr .r5)
  have a4 : WordReadyU 4 a := (ready_set5 _ _ _).mpr ((ready_stepNew _ _ _).mpr h4)
  have b8 : WordReadyU 8 b := by
    apply (ready_set5 _ _ _).mpr
    apply (ready_stepNew _ _ _).mpr
    exact (ready_set5 _ _ _).mpr ((ready_stepNew _ _ _).mpr h8)
  have c12 : WordReadyU 12 c := by
    exact (ready_set5 _ _ _).mpr ((ready_stepNew _ _ _).mpr
      ((ready_set5 _ _ _).mpr ((ready_stepNew _ _ _).mpr
        ((ready_set5 _ _ _).mpr ((ready_stepNew _ _ _).mpr h12)))))
  have e0 := rowFirstAtU_exec (by decide : 0 < 4096) s h0.1 h0.2
  have e4 := rowFirstAtU_exec (by decide : 4 < 4096) a a4.1 a4.2
  have e8 := rowFirstAtU_exec (by decide : 8 < 4096) b b8.1 b8.2
  have e12 := rowStepU_exec (by decide : 12 < 4096) c c12.1 c12.2
  change execBlock isa (rowFirstAtU 0 ++ (rowFirstAtU 4 ++ (rowFirstAtU 8 ++ (rowStepU 12 ++ rowAdvance4)))) s = _
  rw [execBlock_append, e0]
  simp only [Option.bind_some]
  change (execBlock isa (rowFirstAtU 4 ++ (rowFirstAtU 8 ++ (rowStepU 12 ++ rowAdvance4))) a).map _ = _
  rw [execBlock_append, e4]
  simp only [Option.bind_some]
  change ((execBlock isa (rowFirstAtU 8 ++ (rowStepU 12 ++ rowAdvance4)) b).map _).map _ = _
  rw [execBlock_append, e8]
  simp only [Option.bind_some]
  change (((execBlock isa (rowStepU 12 ++ rowAdvance4) c).map _).map _).map _ = _
  rw [execBlock_append, e12, Option.bind_some, advState4_exec]
  simp only [Option.map_some, List.append_nil]
  have stateEq : stepNew 12 c = stepNew 12 (stepNew 8 (stepNew 4 (stepNew 0 s))) := by
    simp only [c, b, a, stepNew_set5]
  rw [stateEq]
  congr 2

end VG.Proof.Bignum.Arm
