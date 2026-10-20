module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Classify
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.LoopState
import VerifiedGarbage.Proof.Framework.Omega

/-! Total correctness of the bounded native FFDH key-search loop, composing
the chosen backend's key-generation attempt. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Spec.Ffdh
open VG.Proof.Ffdh.KeyGeneration

def KeyInvariant (p : KeyPublic) (original : State) (expected : KeySearchResult)
    (n : Nat) (s : State) : Prop :=
  ∃ used keys scalars, n = 128 * keys + scalars + 1 ∧ KeyLive p original used keys scalars s ∧
    expected.outcome = (p.tail (keyRand p original) used keys scalars).outcome ∧
    expected.used = (p.tail (keyRand p original) used keys scalars).used

theorem iteration (backend : VG.Proof.Ffdh.Arm.Backend) (runAttempt : AttemptRunOk backend)
    {p : KeyPublic} {original s : State} {expected : KeySearchResult} {n : Nat}
    (inv : KeyInvariant p original expected n s) :
    WP isa (VG.Impl.Ffdh.Arm.KeySearch.iteration (.call backend.keyName backend.generateKey)) s fun t =>
      (isa.eval .eq t = some false ∧ KeyDone p original expected t) ∨
      (isa.eval .eq t = some true ∧ ∃ m < n, KeyInvariant p original expected m t) := by
  obtain ⟨used, keys, scalars, measure, h, outcome, count⟩ := inv
  have length := h.rand_length
  have done : ∀ (result : KeySearchResult) t, KeyDone p original result t →
      result.outcome = (p.tail (keyRand p original) used keys scalars).outcome →
      result.used = (p.tail (keyRand p original) used keys scalars).used →
      WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r9 14, .cmp .r9 (.imm 4)]) t fun t =>
        (isa.eval .eq t = some false ∧ KeyDone p original expected t) ∨
        (isa.eval .eq t = some true ∧ ∃ m < n, KeyInvariant p original expected m t) :=
    fun _ _ finished resultOutcome resultUsed => WP.mono finished.loop_guard fun _ ⟨flag, state⟩ =>
      Or.inl ⟨flag, state.congr (resultOutcome.trans outcome.symm) (resultUsed.trans count.symm)⟩
  unfold VG.Impl.Ffdh.Arm.KeySearch.iteration VG.Impl.Ffdh.Arm.KeySearch.branch
  refine WP.seq (WP.mono h.keys_guard fun u ⟨live1, flag1⟩ => ?_)
  apply WP.seq
  refine WP.ite (decide (keys = 0)) (by change some u.z = _; rw [flag1]) ?_ ?_
  · intro zero
    have zero' := of_decide_eq_true zero
    refine WP.mono live1.exhausted fun t finished => done _ t finished ?_ ?_ <;>
      simp only [KeyPublic.tail, keyTail_exhausted (Or.inl zero'), exhaustedResult]
  intro nonzero
  have keysNonzero : keys ≠ 0 := of_decide_eq_false nonzero
  refine WP.seq (WP.mono live1.scalars_guard fun u ⟨live2, flag2⟩ => ?_)
  refine WP.ite (decide (scalars = 0)) (by change some u.z = _; rw [flag2]) ?_ ?_
  · intro zero
    have zero' := of_decide_eq_true zero
    refine WP.mono live2.exhausted fun t finished => done _ t finished ?_ ?_ <;>
      simp only [KeyPublic.tail, keyTail_exhausted (Or.inr zero'), exhaustedResult]
  intro nonzero2
  have scalarsNonzero : scalars ≠ 0 := of_decide_eq_false nonzero2
  unfold VG.Impl.Ffdh.Arm.KeySearch.attemptOrRequest
  refine WP.seq (WP.mono live2.room_guard fun u ⟨live3, roomFlag⟩ => ?_)
  refine WP.ite _ (by change some u.z = _; rw [roomFlag]) ?_ ?_
  · intro short
    have short' : (keyRand p original).length - used < p.len := by
      rw [length]; exact of_decide_eq_true short
    refine WP.mono live3.request fun t finished => done _ t finished ?_ ?_ <;>
      simp only [KeyPublic.tail, keyTail_short keysNonzero scalarsNonzero short', requestResult]
  intro enough
  have room : used + p.len ≤ p.randLen := by
    have := of_decide_eq_false enough
    have := h.used_le
    omega
  have room' : p.len ≤ (keyRand p original).length - used := by rw [length]; omega
  refine WP.seq (WP.mono (runAttempt p original u used keys scalars live3 room) fun t ⟨live, post⟩ => ?_)
  refine WP.mono (classify live room (Nat.pos_of_ne_zero keysNonzero)
    (Nat.pos_of_ne_zero scalarsNonzero) post) fun q classified => ?_
  rcases currentStatus_cases p original used with h1 | h2 | h3
  · simp only [KeyClassified, h1, ite_true] at classified
    refine done _ q classified ?_ ?_ <;>
      simp only [KeyPublic.tail, keyTail_accepted keysNonzero scalarsNonzero room' h1, acceptedResult] <;> rfl
  · simp only [KeyClassified, h2, Nat.reduceEqDiff, ite_true, ite_false] at classified
    refine WP.mono (classified.1.loop_guard classified.2) fun z ⟨flag, state⟩ =>
      Or.inr ⟨flag, _, ?_, used + p.len, keys, scalars - 1, rfl, state, ?_, ?_⟩
    · omega
    · rw [outcome]; simp only [KeyPublic.tail, keyTail_scalar keysNonzero scalarsNonzero room' h2]
    · rw [count]; simp only [KeyPublic.tail, keyTail_scalar keysNonzero scalarsNonzero room' h2]
  · simp only [KeyClassified, h3, Nat.reduceEqDiff, ite_false] at classified
    refine WP.mono (classified.1.loop_guard classified.2) fun z ⟨flag, state⟩ =>
      Or.inr ⟨flag, _, ?_, used + p.len, keys - 1, 128, rfl, state, ?_, ?_⟩
    · omega
    · rw [outcome]; simp only [KeyPublic.tail, keyTail_public keysNonzero scalarsNonzero room' h3]
    · rw [count]; simp only [KeyPublic.tail, keyTail_public keysNonzero scalarsNonzero room' h3]

theorem loop (backend : VG.Proof.Ffdh.Arm.Backend) (runAttempt : AttemptRunOk backend)
    {p : KeyPublic} {original s : State} {expected : KeySearchResult} {n : Nat}
    (inv : KeyInvariant p original expected n s) :
    WP isa (.loop (VG.Impl.Ffdh.Arm.KeySearch.iteration (.call backend.keyName backend.generateKey)) .eq)
      s (KeyDone p original expected) :=
  WP.loop (M := isa)
    (body := VG.Impl.Ffdh.Arm.KeySearch.iteration (.call backend.keyName backend.generateKey)) (c := .eq)
    (Q := KeyDone p original expected) (KeyInvariant p original expected)
    (fun _ _ h => iteration backend runAttempt h) n s inv

end VG.Proof.Ffdh.Arm.KeySearch
