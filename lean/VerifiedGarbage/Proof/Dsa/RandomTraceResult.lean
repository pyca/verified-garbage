module
public import VerifiedGarbage.Proof.Dsa.RandomResult

import Std.Data.DTreeMap.Internal.Balancing
import VerifiedGarbage.Proof.Framework.Omega

/-! Scalar presence, status, and consumed bytes are fixed by the public trace. -/
@[expose] public section
namespace VG.Proof.Dsa.Random
open VG.Spec.Dsa.Random

theorem sample_trace_result (q fuel : Nat) (rand : List VG.Byte) :
    (sample q fuel rand).used = drawBytes q * (sample q fuel rand).trace.countP (· ≤ 1) ∧
      (sample q fuel rand).scalar.isSome = ((sample q fuel rand).trace.getLast? == some 1) := by
  induction fuel generalizing rand with
  | zero => simp [sample]
  | succ fuel ih =>
    rw [sample]
    split
    · simp
    · dsimp only
      split
      · simp
      · split
        · simp
        · dsimp only
          obtain ⟨hu, hs⟩ := ih (rand.drop (drawBytes q))
          rw [List.countP_cons_of_pos (by decide),
            List.getLast?_cons_of_ne_nil (sample_trace_nonempty _ _ _)]
          exact ⟨by rw [hu, Nat.mul_add, Nat.mul_one, Nat.add_comm], hs⟩

theorem sample_status_trace (q fuel : Nat) (rand : List VG.Byte) :
    sampleStatus (sample q fuel rand) =
      if (sample q fuel rand).trace.getLast? == some 1 then 1
      else if (sample q fuel rand).trace.getLast? == some 2 then 2 else 0 := by
  have hh := (sample_trace_result q fuel rand).2
  unfold sampleStatus
  cases hc : (sample q fuel rand).scalar with
  | none =>
    rw [hc] at hh
    rw [← hh]
    rfl
  | some k =>
    rw [hc] at hh
    rw [← hh]
    rfl

theorem sample_trace_agree {q fuel : Nat} {a b : List VG.Byte}
    (h : (sample q fuel a).trace = (sample q fuel b).trace) :
    (sample q fuel a).used = (sample q fuel b).used ∧
      (sample q fuel a).scalar.isSome = (sample q fuel b).scalar.isSome ∧
      sampleStatus (sample q fuel a) = sampleStatus (sample q fuel b) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [(sample_trace_result q fuel a).1, (sample_trace_result q fuel b).1, h]
  · rw [(sample_trace_result q fuel a).2, (sample_trace_result q fuel b).2, h]
  · rw [sample_status_trace, sample_status_trace, h]

end VG.Proof.Dsa.Random
