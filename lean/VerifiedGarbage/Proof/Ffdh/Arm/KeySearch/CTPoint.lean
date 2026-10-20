module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.LoopState
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.AttemptPost

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
    (rand := keyRand q.inputs original) (used := q.used) keys scalars (by rw [h.rand_length]; omega)
  rw [statuses] at head
  simp only [KeyPoint.status, head, Option.getD_some]

end VG.Proof.Ffdh.Arm.KeySearch
