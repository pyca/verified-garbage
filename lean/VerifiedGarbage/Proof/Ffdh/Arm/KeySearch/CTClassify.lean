module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTAttempt
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTLeaf
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Classify
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Arm.Taint
meta import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint

/-! Native classification branches depend only on the disclosed attempt
status, with no additional dependence on the private scalar or public value. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm

theorem key_attempted_pins : Pins KeyAttempted [.r4] := by
  intro q s t ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact h₁.pointer.trans h₂.pointer.symm

def KeyGuard (k : Nat) (q : KeyPoint) (s : State) : Prop :=
  KeyAny q.inputs s ∧ s.gpr .r9 = BitVec.ofNat 32 q.status ∧
    isa.eval .eq s = some (decide (q.status = k)) ∧ q.status < 4

private theorem first_ready (q : KeyPoint) (s : State) (h : KeyAttempted q s) :
    WP isa (.block (VG.Impl.Ffdh.Arm.KeySearch.advance ++ [.cmp .r9 (.imm 1)])) s (KeyGuard 1 q) := by
  obtain ⟨original, live, statuses, keys, scalars, room, post⟩ := h
  have disclosed := attempt_status live statuses keys scalars room
  have small : q.status < 4 := by
    rw [← disclosed]
    rcases currentStatus_cases q.inputs original q.used with eq | eq | eq <;> omega
  refine WP.mono (classify_head live room post) ?_
  rintro t ⟨ready, flag, value, _⟩
  refine ⟨⟨original, _, _, _, ready⟩, ?_, ?_, small⟩
  · rw [value, disclosed]
  · change some t.z = _
    rw [flag, disclosed]

private theorem next_ready (j k : Nat) (small : k < 4) (q : KeyPoint) (s : State)
    (h : KeyGuard j q s ∧ isa.eval .eq s = some false) :
    WP isa (.block [.cmp .r9 (.imm (BitVec.ofNat 32 k))]) s (KeyGuard k q) := by
  obtain ⟨⟨⟨original, used, keys, scalars, live⟩, value, _, bound⟩, _⟩ := h
  refine WP.mono (compareStatus_ok s bound small value) ?_
  rintro t ⟨⟨flag, mem⟩, rest⟩
  refine ⟨⟨original, _, _, _, live.keep rest mem⟩, (rest.gpr .r9 (by simp)).trans value, ?_, bound⟩
  change some t.z = _
  rw [flag]

private theorem leaf {k : Nat} {b : Bool} {code : Prog isa}
    (ct : RelCT isa (Two KeyAny) code (fun _ _ => True)) :
    RelCT isa (Two fun q s => KeyGuard k q s ∧ isa.eval .eq s = some b) code (fun _ _ => True) :=
  ct.mono (fun _ _ ⟨q, h₁, h₂, sp⟩ => ⟨q.inputs, h₁.1.1, h₂.1.1, sp⟩) (fun _ _ h => h)

private theorem guard_eq (k : Nat) (q : KeyPoint) (s t : State) (h₁ : KeyGuard k q s) (h₂ : KeyGuard k q t) :
    isa.eval .eq s = isa.eval .eq t := h₁.2.2.1.trans h₂.2.2.1.symm

private theorem no_pins {Φ : KeyPoint → State → Prop} : Pins Φ [] := fun _ _ _ _ _ _ h => by cases h

theorem classify_ct : RelCT isa (Two KeyAttempted) VG.Impl.Ffdh.Arm.KeySearch.classify (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.KeySearch.classify
  refine RelCT.seq (two_piece [.r4] key_attempted_pins (by taint_decide) first_ready) ?_
  refine two_ite (guard_eq 1) (leaf accepted_ct) ?_
  refine RelCT.seq (two_post (two_taint [] no_pins (by taint_decide)) (next_ready 1 2 (by decide))) ?_
  refine two_ite (guard_eq 2) (leaf rejected_scalar_ct) ?_
  refine RelCT.seq (two_post (two_taint [] no_pins (by taint_decide)) (next_ready 2 3 (by decide))) ?_
  exact two_ite (guard_eq 3) (leaf rejected_public_ct) (leaf exhausted_ct)

end VG.Proof.Ffdh.Arm.KeySearch
