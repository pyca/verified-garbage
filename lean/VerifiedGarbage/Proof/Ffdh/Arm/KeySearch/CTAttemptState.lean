module

import VerifiedGarbage.Proof.Framework.Arm.Syms

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTPoint
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Allocated
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Arguments
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.AttemptPost
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend

/-! Before allocation, after argument setup, and after a native key attempt,
with the disclosed attempt-status sequence retained in the proof state. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

def KeyReady (q : KeyPoint sampling) (s : State) : Prop :=
  KeyCTL q s ∧ q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen

def KeyAllocated (q : KeyPoint sampling) (u : State) : Prop := ∃ s, KeyReady q s ∧ u = allocated (GenerationPolicy.argumentBytes sampling) s

def KeyCallCT (q : KeyPoint sampling) (u : State) : Prop :=
  ∃ original s, KeyLive q.inputs original q.used q.keys q.scalars s ∧
    (q.inputs.tail (keyRand q.inputs original) q.used q.keys q.scalars).statuses = q.statuses ∧
    q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen ∧
    ArgumentContext q.inputs q.used q.keys q.scalars u ∧
    u.mem = callMem q.inputs q.used s.mem (callSp q.inputs) ∧
    Rest [.r0, .r1, .r2, .r3, .r9, .r12] (allocated (GenerationPolicy.argumentBytes sampling) s) u ∧ u.syms = s.syms

def KeyAttempted (q : KeyPoint sampling) (t : State) : Prop :=
  ∃ original, KeyLive q.inputs original q.used q.keys q.scalars t ∧
    (q.inputs.tail (keyRand q.inputs original) q.used q.keys q.scalars).statuses = q.statuses ∧
    q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen ∧
    AttemptPost q.inputs original q.used t

theorem key_allocated_pins : Pins (KeyAllocated (sampling := sampling)) [.r4] := by
  rintro q _ _ ⟨s, ⟨⟨_, h₁, _⟩, _⟩, rfl⟩ ⟨t, ⟨⟨_, h₂, _⟩, _⟩, rfl⟩ r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h₁.pointer.trans h₂.pointer.symm

theorem arguments_ready (q : KeyPoint sampling) (u : State) (h : KeyAllocated q u) :
    WP isa (.block (VG.Impl.Ffdh.Arm.KeySearch.argumentsFor sampling.cachedContext)) u (KeyCallCT q) := by
  obtain ⟨s, ⟨⟨original, live, statuses⟩, keys, scalars, room⟩, rfl⟩ := h
  obtain ⟨control, stack, separate⟩ := live.allocated_data
  have sep : (rControl q.inputs).Disjoint ⟨State.addr (allocated (GenerationPolicy.argumentBytes sampling) s).sp, sampling.argumentBytes⟩ := by
    rw [live.call_sp]; exact separate
  refine WP.mono_syms (arguments_ok (allocated (GenerationPolicy.argumentBytes sampling) s) control stack sep live.headers live.cachedSlots) ?_
  rintro t ⟨⟨args, mem⟩, rest⟩ syms
  refine ⟨original, s, live, statuses, keys, scalars, room, args, ?_, rest, syms⟩
  rw [mem, live.call_sp]
  rfl


end VG.Proof.Ffdh.Arm.KeySearch
