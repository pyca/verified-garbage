module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.AttemptPost
import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Live
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Contract
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Geometry

/-! ### `Ffdh.Arm.KeySearch.LoopState`, which this module and modules that import it used -/

section

/-! The search result depends on its outcome and consumed bytes; its public
status controls the native loop's continuation flag. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Spec.Ffdh

theorem KeyDone.congr {p : KeyPublic sampling} {original s : State} {result expected : KeySearchResult}
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

theorem KeyLive.rand_length {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}
    (_h : KeyLive p original used keys scalars s) : (keyRand p original).length = p.randLen :=
  by simp only [keyRand, Spec.Rsa.bytesAt, List.length_map, List.length_range]

theorem KeyLive.loop_guard {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (status : lowWord s.mem p.control 14 = 4) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r9 14, .cmp .r9 (.imm 4)]) s fun t =>
      isa.eval .eq t = some true ∧ KeyLive p original used keys scalars t := by
  refine WP.mono_syms (statusGuard_ok s (status := 4) h.controller (by decide) status) ?_
  rintro t ⟨⟨flag, mem⟩, rest⟩ syms
  refine ⟨?_, h.keep rest mem syms⟩
  change some t.z = some true
  rw [flag]
  rfl

theorem KeyDone.loop_guard {p : KeyPublic sampling} {original s : State} {result : KeySearchResult}
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
def AttemptRunOk (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) : Prop :=
  ∀ (p : KeyPublic sampling) (original s : State) (used keys scalars : Nat),
    KeyLive p original used keys scalars s → used + p.len ≤ p.randLen →
      WP isa (VG.Impl.Ffdh.Arm.KeySearch.attemptRunFor sampling.cachedContext (.call backend.keyName backend.generateKey)) s fun t =>
        KeyLive p original used keys scalars t ∧ AttemptPost p original used t

end VG.Proof.Ffdh.Arm.KeySearch

end

end

/-! The public point of a native search: descriptor, consumed bytes,
retry budgets, and disclosed attempt statuses still to come. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm
open VG.Proof.Ffdh.GenerationSearch

def KeyAny (p : KeyPublic sampling) (s : State) : Prop :=
  ∃ original used keys scalars, KeyLive p original used keys scalars s

structure KeyPoint (sampling : VG.Proof.Ffdh.GenerationPolicy) where
  inputs : KeyPublic sampling
  used : Nat
  keys : Nat
  scalars : Nat
  statuses : List Nat

def KeyCTL (q : KeyPoint sampling) (s : State) : Prop :=
  ∃ original, KeyLive q.inputs original q.used q.keys q.scalars s ∧
    (q.inputs.tail (keyRand q.inputs original) q.used q.keys q.scalars).statuses = q.statuses

theorem KeyCTL.any {q : KeyPoint sampling} {s : State} (h : KeyCTL q s) : KeyAny q.inputs s :=
  let ⟨original, live, _⟩ := h; ⟨original, _, _, _, live⟩

theorem key_any_pins : Pins (KeyAny (sampling := sampling)) [.r4] := by
  intro p s t ⟨_, _, _, _, h₁⟩ ⟨_, _, _, _, h₂⟩ r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h₁.pointer.trans h₂.pointer.symm

theorem key_ctl_pins : Pins (KeyCTL (sampling := sampling)) [.r4] :=
  fun _ _ _ h₁ h₂ => key_any_pins _ _ _ h₁.any h₂.any

def KeyPoint.status (q : KeyPoint sampling) : Nat := q.statuses.head?.getD 0

theorem attempt_status {q : KeyPoint sampling} {original s : State}
    (h : KeyLive q.inputs original q.used q.keys q.scalars s)
    (statuses : (q.inputs.tail (keyRand q.inputs original) q.used q.keys q.scalars).statuses = q.statuses)
    (keys : q.keys ≠ 0) (scalars : q.scalars ≠ 0) (room : q.used + q.inputs.len ≤ q.inputs.randLen) :
    currentStatus q.inputs original q.used = q.status := by
  have head := keyTail_statuses_head (policy := sampling) (a := q.inputs.a) (len := q.inputs.len)
    (rand := keyRand q.inputs original) (used := q.used) keys scalars (by rw [h.rand_length]; omega_using [room])
  rw [statuses] at head
  simp only [KeyPoint.status, head, Option.getD_some]

end VG.Proof.Ffdh.Arm.KeySearch
