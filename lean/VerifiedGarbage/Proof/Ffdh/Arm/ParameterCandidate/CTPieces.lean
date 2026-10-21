module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! Public addresses and loop counts for native candidate byte operations. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm

abbrev CandidateCert (rs : List Reg) (code : Prog isa) : Prop :=
  ∃ hint, (VG.Taint.check taint (Taint.ofRegs rs) code hint).isSome = true

theorem copyLoop_taint : CandidateCert [.r0, .r1, .lr] VG.Impl.Bignum.Arm.copyBytes := ⟨_, by taint_decide⟩

theorem maskLoop_taint : CandidateCert [.r6]
    (.loop (.block VG.Impl.Ffdh.Arm.ParameterCandidate.maskStep) .ne) := ⟨_, by taint_decide⟩

theorem maskHeadTail_taint : CandidateCert [.r6]
    (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.shapeMaskHead.drop 1)) := ⟨_, by taint_decide⟩

theorem shapeFirstTail_taint : CandidateCert [.r4]
    (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.shapeFirst.drop 1)) := ⟨_, by taint_decide⟩

theorem shapeLastTail_taint : CandidateCert [.r4, .r5]
    (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.shapeLast.drop 1)) := ⟨_, by taint_decide⟩

theorem tableWrites_taint : CandidateCert [.r11]
    (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrites 1024)) := ⟨_, by taint_decide⟩

theorem sieveEntry_taint : CandidateCert [.r10]
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveEntry) := ⟨_, by taint_decide⟩

theorem clearOutputLoop_taint : CandidateCert [.r0, .lr] VG.Impl.Ffdh.Arm.Domain.GenerateKey.zeros := ⟨_, by taint_decide⟩

theorem finishTail_taint (status : Nat) (bound : status ≤ 2) : CandidateCert [.r2]
    (.block ((VG.Impl.Ffdh.Arm.ParameterCandidate.finish status).drop 1)) := by
  rcases (by omega : status = 0 ∨ status = 1 ∨ status = 2) with rfl | rfl | rfl <;> exact ⟨_, by taint_decide⟩

theorem halveLoop_taint : CandidateCert [.r0, .lr]
    (.loop (.block VG.Impl.Ffdh.Arm.ParameterCandidate.halfByte) .ne) := ⟨_, by taint_decide⟩

theorem trialDigit_taint : CandidateCert [.r0, .r1] VG.Impl.Ffdh.Arm.ParameterCandidate.trialDigit := ⟨_, by taint_decide⟩

theorem trialLoop_taint : CandidateCert [.r0, .r1]
    (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.trialStep .ne) := ⟨_, by taint_decide⟩

theorem trialFlag_taint : CandidateCert [.r2] VG.Impl.Ffdh.Arm.ParameterCandidate.trialFlag := ⟨_, by taint_decide⟩

theorem residue2Equals_taint : CandidateCert [.r2]
    (VG.Impl.Ffdh.Arm.ParameterCandidate.residueEquals [2, 5]) := ⟨_, by taint_decide⟩

theorem residue5Equals_taint : CandidateCert [.r2]
    (VG.Impl.Ffdh.Arm.ParameterCandidate.residueEquals [2, 3, 7, 8]) := ⟨_, by taint_decide⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
