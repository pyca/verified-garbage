module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTKeyRegisters
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPolicy
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTKeyRegisters
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! Native decomposition steps expose only fixed stack slots and public RSA array-view addresses. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm

private theorem half29_taint : CandidateCert keyRegs (VG.Impl.Rsa.Arm.Keys.half 29) := ⟨_, by taint_decide⟩
private theorem copy29_taint : CandidateCert keyRegs (VG.Impl.Rsa.Arm.Keys.copy 29 0) := ⟨_, by taint_decide⟩
private theorem clear29_taint : CandidateCert keyRegs (.block (VG.Impl.Rsa.Arm.Keys.clrLow 29)) := ⟨_, by taint_decide⟩
private theorem countTail_taint : CandidateCert keyRegs
    (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountTail.drop 4)) := ⟨_, by taint_decide⟩

private theorem countTail_ct : RelCT isa KeyRegEq (.block VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountTail) KeyRegEq := by
  have countHead : RelCT isa (fun s t => s.sp = t.sp)
      (.block (([.ldrSp .r1 60, .dp .add .r1 .r1 (.imm 1)] : List Instr) ++ VG.Impl.Ffdh.Arm.ParameterCandidate.save .r1 60))
      (fun s t => s.sp = t.sp) :=
    RelCT.block_append ((stackOnly_ct [.ldrSp .r1 60, .dp .add .r1 .r1 (.imm 1)] rfl).seq (save_ct .r1 60))
  change RelCT isa KeyRegEq (.block (([.ldrSp .r1 60, .dp .add .r1 .r1 (.imm 1)] ++
    VG.Impl.Ffdh.Arm.ParameterCandidate.save .r1 60) ++ VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountTail.drop 4)) KeyRegEq
  exact RelCT.block_append ((keyRegs_stack_ct countHead (by decide) (by decide)).seq
    (keyRegs_taint_ct countTail_taint (by decide) (by decide)))

theorem halfCountStep_ct : RelCT isa KeyRegEq VG.Impl.Ffdh.Arm.ParameterCandidate.halfCountStep KeyRegEq :=
  (keyRegs_stack_ct (stackOnly_ct [.mov .r11 (.imm 0)] rfl) (by decide) (by decide)).seq
    ((keyRegs_taint_ct half29_taint (by decide) (by decide)).seq
      (countTail_ct.seq (RelCT.block_nil (fun _ _ h => h))))

theorem expCountInit_ct : RelCT isa KeyRegEq VG.Impl.Ffdh.Arm.ParameterCandidate.expCountInit KeyRegEq :=
  (keyRegs_taint_ct copy29_taint (by decide) (by decide)).seq
    ((keyRegs_taint_ct clear29_taint (by decide) (by decide)).seq
      ((keyRegs_stack_ct (saveWord_ct .r1 60 0) (by decide) (by decide)).seq
        (RelCT.block_nil (fun _ _ h => h))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
