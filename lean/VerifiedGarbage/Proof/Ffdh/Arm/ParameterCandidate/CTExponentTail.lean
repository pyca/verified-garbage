module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTExponentLoop
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTKeyRegisters
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
meta import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTKeyRegisters
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! Fixed-step exponent metadata and public-address array storage. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two)

private theorem powerStore_taint : CandidateCert keyRegs
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.exponentPowerStore) := ⟨_, by taint_decide⟩

theorem exponentPower_ct : RelCT isa KeyRegEq
    (.seq (.block (([.ldrSp .r1 60] : List Instr) ++ VG.Impl.Bignum.Arm.TwoPower.code))
      (.seq (.block VG.Impl.Ffdh.Arm.ParameterCandidate.exponentPowerStore) (.block [])))
    (fun _ _ => True) := by
  refine (keyRegs_stack_ct (stackOnly_ct _ rfl) (by decide) (by decide)).seq ?_
  obtain ⟨hint, checked⟩ := powerStore_taint
  exact (RelCT.taint (A := taint) (Taint.ofRegs keyRegs)
    (fun _ _ h => Taint.agree_ofRegs h.1) checked).seq (RelCT.block_nil (fun _ _ _ => trivial))

theorem exponentHalfLoop_key_ct : RelCT isa (Two ExponentCountState)
    (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.exponentHalf .ne) KeyRegEq := by
  refine keyRegs_keep_ct exponentHalfLoop_ct ?_ (by decide) (by decide)
  rintro s t ⟨p, left, right, sp⟩
  refine ⟨?_, sp⟩
  intro r hr
  simp only [keyRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact left.ready.r7.trans right.ready.r7.symm
  · exact left.ready.r8.trans right.ready.r8.symm
  · exact left.ready.r9.trans right.ready.r9.symm

end VG.Proof.Ffdh.Arm.ParameterCandidate
