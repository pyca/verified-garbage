module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.AttemptPost
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Live
import VerifiedGarbage.Proof.Framework.Offset

/-! The search result depends on its outcome and consumed bytes; its public
status controls the native loop's continuation flag. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Spec.Ffdh

theorem KeyDone.congr {p : KeyPublic} {original s : State} {result expected : KeySearchResult}
    (h : KeyDone p original result s) (outcome : result.outcome = expected.outcome)
    (used : result.used = expected.used) : KeyDone p original expected s := by
  have status : result.status = expected.status := by unfold KeySearchResult.status; rw [outcome]
  have retries : result.retries = expected.retries := by unfold KeySearchResult.retries; rw [outcome]
  refine ⟨h.input, by rw [← used]; exact h.used_le, h.rd, h.wr, h.sp, h.pointer, h.kept, h.saved, h.usedPtr,
    by rw [← used]; exact h.used, by rw [← status]; exact h.status, ?_, ?_⟩
  · rw [h.policy, status, retries]
  · have output := h.output
    unfold KeyOutput at output ⊢
    rw [← outcome]
    exact output

theorem KeyLive.rand_length {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (_h : KeyLive p original used keys scalars s) : (keyRand p original).length = p.randLen :=
  by simp only [keyRand, Spec.Rsa.bytesAt, List.length_map, List.length_range]

theorem KeyLive.loop_guard {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (status : lowWord s.mem p.control 14 = 4) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r9 14, .cmp .r9 (.imm 4)]) s fun t =>
      isa.eval .eq t = some true ∧ KeyLive p original used keys scalars t := by
  refine WP.mono (statusGuard_ok s (status := 4) h.controller (by decide) status) ?_
  rintro t ⟨⟨flag, mem⟩, rest⟩
  refine ⟨?_, h.keep rest mem⟩
  change some t.z = some true
  rw [flag]
  rfl

theorem KeyDone.loop_guard {p : KeyPublic} {original s : State} {result : KeySearchResult}
    (h : KeyDone p original result s) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r9 14, .cmp .r9 (.imm 4)]) s fun t =>
      isa.eval .eq t = some false ∧ KeyDone p original result t := by
  have small : result.status < 5 := by cases outcome : result.outcome <;> simp [KeySearchResult.status, outcome]
  have different : result.status ≠ 4 := by cases outcome : result.outcome <;> simp [KeySearchResult.status, outcome]
  refine WP.mono (statusGuard_ok s h.controller small h.status) ?_
  rintro t ⟨⟨flag, mem⟩, rest⟩
  refine ⟨?_, h.keep rest mem⟩
  change some t.z = some false
  rw [flag, show decide (result.status = 4) = false from decide_eq_false different]

/-- A verified implementation of the chosen backend's nested attempt call. -/
def AttemptRunOk (backend : VG.Proof.Ffdh.Arm.Backend) : Prop :=
  ∀ (p : KeyPublic) (original s : State) (used keys scalars : Nat),
    KeyLive p original used keys scalars s → used + p.len ≤ p.randLen →
      WP isa (VG.Impl.Ffdh.Arm.KeySearch.attemptRun (.call backend.keyName backend.generateKey)) s fun t =>
        KeyLive p original used keys scalars t ∧ AttemptPost p original used t

end VG.Proof.Ffdh.Arm.KeySearch
