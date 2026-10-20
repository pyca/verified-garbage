module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTPoint
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Allocated
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Arguments
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.AttemptPost
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Call
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallRegions

/-! Before allocation, after argument setup, and after a native key attempt,
with the disclosed attempt-status sequence retained in the proof state. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

def KeyReady (q : KeyPoint) (s : State) : Prop :=
  KeyCTL q s ∧ q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen

def KeyAllocated (q : KeyPoint) (u : State) : Prop := ∃ s, KeyReady q s ∧ u = allocated 32 s

def KeyCallCT (q : KeyPoint) (u : State) : Prop :=
  ∃ original s, KeyLive q.inputs original q.used q.keys q.scalars s ∧
    (q.inputs.tail (keyRand q.inputs original) q.used q.keys q.scalars).statuses = q.statuses ∧
    q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen ∧
    ArgumentContext q.inputs q.used q.keys q.scalars u ∧
    u.mem = callMem q.inputs q.used s.mem (callSp q.inputs) ∧
    Rest [.r0, .r1, .r2, .r3, .r9, .r12] (allocated 32 s) u

def KeyAttempted (q : KeyPoint) (t : State) : Prop :=
  ∃ original, KeyLive q.inputs original q.used q.keys q.scalars t ∧
    (q.inputs.tail (keyRand q.inputs original) q.used q.keys q.scalars).statuses = q.statuses ∧
    q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen ∧
    AttemptPost q.inputs original q.used t

theorem key_allocated_pins : Pins KeyAllocated [.r4] := by
  rintro q _ _ ⟨s, ⟨⟨_, h₁, _⟩, _⟩, rfl⟩ ⟨t, ⟨⟨_, h₂, _⟩, _⟩, rfl⟩ r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h₁.pointer.trans h₂.pointer.symm

theorem arguments_ready (q : KeyPoint) (u : State) (h : KeyAllocated q u) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.arguments) u (KeyCallCT q) := by
  obtain ⟨s, ⟨⟨original, live, statuses⟩, keys, scalars, room⟩, rfl⟩ := h
  obtain ⟨control, stack, separate⟩ := live.allocated_data
  have sep : (rControl q.inputs).Disjoint ⟨State.addr (allocated 32 s).sp, 32⟩ := by
    rw [live.call_sp]; exact separate
  refine WP.mono (arguments_ok (allocated 32 s) control stack sep live.headers) ?_
  rintro t ⟨⟨args, mem⟩, rest⟩
  refine ⟨original, s, live, statuses, keys, scalars, room, args, ?_, rest⟩
  rw [mem, live.call_sp]
  rfl

theorem attempt_ready (backend : VG.Proof.Ffdh.Arm.KeyBackend) (q : KeyPoint) (s : State) (h : KeyReady q s) :
    WP isa (VG.Impl.Ffdh.Arm.KeySearch.attemptRun (.call backend.keyName backend.generateKey)) s (KeyAttempted q) := by
  obtain ⟨⟨original, live, statuses⟩, keys, scalars, room⟩ := h
  exact WP.mono (attemptRun_ok backend q.inputs original s q.used q.keys q.scalars live room)
    fun _ ⟨ready, post⟩ => ⟨original, ready, statuses, keys, scalars, room, post⟩

end VG.Proof.Ffdh.Arm.KeySearch
