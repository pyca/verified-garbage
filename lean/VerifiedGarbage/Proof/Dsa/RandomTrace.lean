module
public import VerifiedGarbage.Spec.Dsa.Random

import VerifiedGarbage.Proof.Dsa.RandomResult
import VerifiedGarbage.Proof.Framework.Omega

/-! Recover individual draw decisions from the specified public sampling trace. -/
@[expose] public section
namespace VG.Proof.Dsa.Random
open VG.Spec.Dsa.Random

theorem sample_trace_head (q fuel : Nat) (rand : List VG.Byte) (hq : 1 < q)
    (hfull : drawBytes q ≤ rand.length) :
    ((sample q (fuel + 1) rand).trace.head? == some 1) =
      decide (0 < candidate q (rand.take (drawBytes q)) ∧ candidate q (rand.take (drawBytes q)) < q) := by
  by_cases ha : 0 < candidate q (rand.take (drawBytes q)) ∧ candidate q (rand.take (drawBytes q)) < q
  · rw [sample_accept q fuel rand hq hfull ha, decide_eq_true ha]
    rfl
  · rw [sample_reject q fuel rand hq hfull ha, decide_eq_false ha]
    rfl

theorem sample_trace_retry (q fuel : Nat) (rand : List VG.Byte) (hq : 1 < q)
    (hfull : drawBytes q ≤ rand.length)
    (ha : ((sample q (fuel + 1) rand).trace.head? == some 1) = false) :
    (sample q (fuel + 1) rand).trace.tail = (sample q fuel (rand.drop (drawBytes q))).trace := by
  have hn := sample_trace_head q fuel rand hq hfull
  rw [ha] at hn
  have hnot : ¬ (0 < candidate q (rand.take (drawBytes q)) ∧ candidate q (rand.take (drawBytes q)) < q) :=
    of_decide_eq_false hn.symm
  rw [sample_reject q fuel rand hq hfull hnot]
  rfl

end VG.Proof.Dsa.Random
