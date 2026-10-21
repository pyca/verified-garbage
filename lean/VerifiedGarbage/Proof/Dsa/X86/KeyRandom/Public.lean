module
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CTDefs
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.Result
import VerifiedGarbage.Proof.Dsa.RandomTraceResult

/-! # The domain and sampling decisions disclosed by the key-generation contract -/
@[expose] public section
namespace VG.Proof.Dsa.X86.KeyRandom
open VG VG.X86

theorem sample_trace_le (q fuel : Nat) (rand : List Byte) :
    ∀ x ∈ (Spec.Dsa.Random.sample q fuel rand).trace, x ≤ 4 := by
  induction fuel generalizing rand with
  | zero => simp [Spec.Dsa.Random.sample]
  | succ fuel ih =>
    rw [Spec.Dsa.Random.sample]
    split
    · simp
    · dsimp only
      split
      · simp
      · split
        · simp
        · intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · decide
          · exact ih _ x hx

theorem draw_trace {s : State} (A : KeyABI s) (hc : checked s = true) :
    (rResult s).trace.filter (fun x => decide (x ≤ 4)) = (draw s).trace := by
  have hle := sample_trace_le (Spec.Dsa.decodeBE (rQBytes s)) 128 (rInput s).rand
  rw [result_eq A, hc]
  simp only [ite_true]
  cases (draw s).scalar with
  | none => exact List.filter_eq_self.mpr fun x hx => decide_eq_true (hle x hx)
  | some k =>
    dsimp only
    rw [List.filter_append, List.filter_eq_self.mpr fun x hx => decide_eq_true (hle x hx)]
    split <;> exact List.append_nil _

theorem checked_eq {s t : State} (e : pubOf s = pubOf t) (hk : (rInput s).key = (rInput t).key) :
    checked s = checked t := by
  unfold checked Spec.Dsa.checkParametersBytes
  rw [hk]
  have hp := congrArg BitVec.toNat (pub_arg e 5 (by decide))
  have hq := congrArg BitVec.toNat (pub_arg e 6 (by decide))
  change (rInput s).pLen = (rInput t).pLen at hp
  change (rInput s).qLen = (rInput t).qLen at hq
  rw [hp, hq]

theorem sample_status_eq {s t : State} (e : pubOf s = pubOf t)
    (htr : (draw s).trace = (draw t).trace) :
    VG.Proof.Dsa.Random.sampleStatus (draw s) = VG.Proof.Dsa.Random.sampleStatus (draw t) := by
  unfold draw at htr ⊢
  rw [pub_qBytes e] at htr ⊢
  exact (VG.Proof.Dsa.Random.sample_trace_agree htr).2.2

end VG.Proof.Dsa.X86.KeyRandom
