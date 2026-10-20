module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTFinish
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Status
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega

/-! Final status dispatch is public; every selected return has a fixed buffer-address trace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_ite two_mono)

def ResultState (p : ResultData × Nat) (s : State) : Prop :=
  ResultStart p.1 s ∧ p.2 ≤ 2 ∧ s.gpr .r3 = BitVec.ofNat 32 p.2

private def ResultCompared (compare : Nat) (p : ResultData × Nat) (s : State) : Prop :=
  ResultState p s ∧ s.z = decide (p.2 = compare)

private theorem resultCompare_ct (compare : Nat) (bound : compare ≤ 4) : RelCT isa (Two ResultState)
    (.block [.cmp .r3 (.imm (BitVec.ofNat 32 compare))]) (Two (ResultCompared compare)) :=
  two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
    refine WP.mono (cmpStatus_ok p.2 compare (by have := h.2.1; omega) bound h.2.2) ?_
    rintro t ⟨⟨zero, memory⟩, rest⟩
    exact ⟨⟨h.1.after_memory memory rest, h.2.1, (rest.gpr .r3 (by simp)).trans h.2.2⟩, zero⟩)

private theorem resultTail_ct : RelCT isa (Two ResultState)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [
      .block [.cmp .r3 (.imm 1)], .ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finAccepted VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected])
    (fun _ _ => True) := by
  have branch : RelCT isa (Two (ResultCompared 1))
      (.ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finAccepted VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected) (fun _ _ => True) := by
    refine two_ite (fun p s t a b => by change some s.z = some t.z; rw [a.2, b.2]) ?_ ?_
    · exact finAccepted_ct.mono
        (fun _ _ ⟨p, a, b, sp⟩ => ⟨p.1, a.1.1.1, b.1.1.1, sp⟩) (fun _ _ h => h)
    · exact finRejected_ct.mono
        (fun _ _ ⟨p, a, b, sp⟩ => ⟨p.1, a.1.1.1, b.1.1.1, sp⟩) (fun _ _ h => h)
  exact (resultCompare_ct 1 (by decide)).seq (branch.seq (RelCT.block_nil (fun _ _ h => h)))

theorem result_ct : RelCT isa (Two ResultState) VG.Impl.Ffdh.Arm.ParameterCandidate.result (fun _ _ => True) := by
  have branch : RelCT isa (Two (ResultCompared 0))
      (.ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finNone (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [
        .block [.cmp .r3 (.imm 1)], .ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finAccepted VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected]))
      (fun _ _ => True) := by
    refine two_ite (fun p s t a b => by change some s.z = some t.z; rw [a.2, b.2]) ?_ ?_
    · exact finNone_ct.mono
        (fun _ _ ⟨p, a, b, sp⟩ => ⟨p.1, a.1.1.1, b.1.1.1, sp⟩) (fun _ _ h => h)
    · exact resultTail_ct.mono (fun _ _ h => two_mono (fun _ _ h => h.1.1) h) (fun _ _ h => h)
  exact (resultCompare_ct 0 (by decide)).seq (branch.seq (RelCT.block_nil (fun _ _ h => h)))

end VG.Proof.Ffdh.Arm.ParameterCandidate
