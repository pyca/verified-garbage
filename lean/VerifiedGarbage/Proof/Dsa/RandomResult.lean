module
public import VerifiedGarbage.Spec.Dsa.Random
import VerifiedGarbage.Proof.Framework.Omega


/-! Observable results of bounded rejection sampling. -/
@[expose] public section
namespace VG.Proof.Dsa.Random
open VG.Spec.Dsa.Random

def sampleStatus (r : Sample) : Nat :=
  match r.scalar with
  | some _ => 1
  | none => if r.trace.getLast? == some 2 then 2 else 0

theorem sample_trace_nonempty (q fuel : Nat) (rand : List VG.Byte) :
    (sample q fuel rand).trace ≠ [] := by
  cases fuel with
  | zero => simp [sample]
  | succ fuel =>
    simp only [sample]
    split
    · simp
    · split
      · simp
      · split <;> simp

theorem sampleStatus_reject (q fuel width : Nat) (rand : List VG.Byte) :
    sampleStatus ⟨(sample q fuel rand).scalar,
      width + (sample q fuel rand).used, 0 :: (sample q fuel rand).trace⟩ =
      sampleStatus (sample q fuel rand) := by
  unfold sampleStatus
  cases (sample q fuel rand).scalar with
  | some k => rfl
  | none =>
    obtain ⟨x, xs, he⟩ := List.exists_cons_of_ne_nil (sample_trace_nonempty q fuel rand)
    rw [he]
    rfl

theorem sample_short (q fuel : Nat) (rand : List VG.Byte) (hq : 1 < q)
    (hs : rand.length < drawBytes q) : sample q (fuel + 1) rand = ⟨none, 0, [2]⟩ := by
  rw [sample, ite_eq_right (by omega), ite_eq_left hs]

theorem sample_accept (q fuel : Nat) (rand : List VG.Byte) (hq : 1 < q)
    (hs : drawBytes q ≤ rand.length)
    (hk : 0 < candidate q (rand.take (drawBytes q)) ∧ candidate q (rand.take (drawBytes q)) < q) :
    sample q (fuel + 1) rand = ⟨some (candidate q (rand.take (drawBytes q))), drawBytes q, [1]⟩ := by
  rw [sample, ite_eq_right (by omega), ite_eq_right (by omega)]
  simp only [hk.1, hk.2, decide_true, Bool.and_self, ite_true]

theorem sample_reject (q fuel : Nat) (rand : List VG.Byte) (hq : 1 < q)
    (hs : drawBytes q ≤ rand.length)
    (hk : ¬ (0 < candidate q (rand.take (drawBytes q)) ∧ candidate q (rand.take (drawBytes q)) < q)) :
    sample q (fuel + 1) rand =
      { sample q fuel (rand.drop (drawBytes q)) with
        used := drawBytes q + (sample q fuel (rand.drop (drawBytes q))).used,
        trace := 0 :: (sample q fuel (rand.drop (drawBytes q))).trace } := by
  rw [sample, ite_eq_right (by omega), ite_eq_right (by omega)]
  simp only [Bool.and_eq_true, decide_eq_true_eq, hk, ite_false]


end VG.Proof.Dsa.Random
