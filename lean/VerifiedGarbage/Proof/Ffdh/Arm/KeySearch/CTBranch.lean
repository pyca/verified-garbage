module

public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Exit
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTClassify
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTAttemptState
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTAttemptState
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeyBackend
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTAttempt
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTAttempt
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTLeaf
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTLeaf
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Call
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Call
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Classify
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Classify
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Live
meta import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Live

/-! Retry-budget and entropy-room guards, and the next disclosed search point. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm
open VG.Proof.Ffdh.GenerationSearch

def keyContinues (q : KeyPoint sampling) : Prop :=
  q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.inputs.len ≤ q.inputs.randLen - q.used ∧ q.status ≠ 1

instance (q : KeyPoint sampling) : Decidable (keyContinues q) := inferInstanceAs
  (Decidable (q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.inputs.len ≤ q.inputs.randLen - q.used ∧ q.status ≠ 1))

def nextKeyPoint (q : KeyPoint sampling) : KeyPoint sampling :=
  if q.status = 2 then ⟨q.inputs, q.used + q.inputs.len, q.keys, q.scalars - 1, q.statuses.tail⟩
  else ⟨q.inputs, q.used + q.inputs.len, q.keys - 1, 128, q.statuses.tail⟩

theorem nextKeyPoint_inputs (q : KeyPoint sampling) : (nextKeyPoint q).inputs = q.inputs := by
  unfold nextKeyPoint; split <;> rfl

theorem nextKeyPoint_measure {q : KeyPoint sampling} (h : keyContinues q) :
    128 * (nextKeyPoint q).keys + (nextKeyPoint q).scalars < 128 * q.keys + q.scalars := by
  obtain ⟨keys, scalars, _, _⟩ := h
  unfold nextKeyPoint; split <;> dsimp only <;> omega

def KeyBranchResult (q : KeyPoint sampling) (s : State) : Prop :=
  if keyContinues q then KeyCTL (nextKeyPoint q) s ∧ lowWord s.mem q.inputs.control 14 = 4
  else ∃ original result, KeyDone q.inputs original result s

theorem branch_pointer {q : KeyPoint sampling} {s : State} (h : KeyBranchResult q s) : s.gpr .r4 = q.inputs.control := by
  by_cases continues : keyContinues q
  · simp only [KeyBranchResult, continues, ite_true] at h
    obtain ⟨⟨_, live, _⟩, _⟩ := h
    rw [live.pointer, nextKeyPoint_inputs]
  · simp only [KeyBranchResult, continues, ite_false] at h
    obtain ⟨_, _, finished⟩ := h
    exact finished.pointer

def KeysGuard (q : KeyPoint sampling) (s : State) : Prop :=
  KeyCTL q s ∧ isa.eval .eq s = some (decide (q.keys = 0))

def ScalarsGuard (q : KeyPoint sampling) (s : State) : Prop :=
  KeyCTL q s ∧ q.keys ≠ 0 ∧ isa.eval .eq s = some (decide (q.scalars = 0))

def RoomGuard (q : KeyPoint sampling) (s : State) : Prop :=
  KeyCTL q s ∧ q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧
    isa.eval .eq s = some (decide (q.inputs.randLen - q.used < q.inputs.len))

theorem keys_ready (q : KeyPoint sampling) (s : State) (h : KeyCTL q s) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r9 0, .cmp .r9 (.imm 0)]) s (KeysGuard q) := by
  obtain ⟨original, live, statuses⟩ := h
  refine WP.mono live.keys_guard ?_
  rintro t ⟨ready, flag⟩
  refine ⟨⟨original, ready, statuses⟩, ?_⟩
  change some t.z = _
  rw [flag]

theorem scalars_ready (q : KeyPoint sampling) (s : State) (h : KeysGuard q s ∧ isa.eval .eq s = some false) :
    WP isa (.block [VG.Impl.Ffdh.Arm.KeySearch.ldf .r9 1, .cmp .r9 (.imm 0)]) s (ScalarsGuard q) := by
  obtain ⟨⟨⟨original, live, statuses⟩, flag⟩, nonzero⟩ := h
  have keys : q.keys ≠ 0 := of_decide_eq_false (Option.some.inj (flag.symm.trans nonzero))
  refine WP.mono live.scalars_guard ?_
  rintro t ⟨ready, flagT⟩
  refine ⟨⟨original, ready, statuses⟩, keys, ?_⟩
  change some t.z = _
  rw [flagT]

theorem room_ready (q : KeyPoint sampling) (s : State) (h : ScalarsGuard q s ∧ isa.eval .eq s = some false) :
    WP isa (.block VG.Impl.Ffdh.Arm.KeySearch.room) s (RoomGuard q) := by
  obtain ⟨⟨⟨original, live, statuses⟩, keys, flag⟩, nonzero⟩ := h
  have scalars : q.scalars ≠ 0 := of_decide_eq_false (Option.some.inj (flag.symm.trans nonzero))
  refine WP.mono live.room_guard ?_
  rintro t ⟨ready, flagT⟩
  refine ⟨⟨original, ready, statuses⟩, keys, scalars, ?_⟩
  change some t.z = _
  rw [flagT]

theorem attempt_of_room {q : KeyPoint sampling} {s : State}
    (h : RoomGuard q s ∧ isa.eval .eq s = some false) : KeyReady q s := by
  obtain ⟨⟨⟨original, live, statuses⟩, keys, scalars, flag⟩, enough⟩ := h
  have room := of_decide_eq_false (Option.some.inj (flag.symm.trans enough))
  exact ⟨⟨original, live, statuses⟩, keys, scalars, by have := live.used_le; omega⟩

theorem branch_ready (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) (q : KeyPoint sampling) (s : State) (h : KeysGuard q s) :
    WP isa ((VG.Impl.Ffdh.Arm.KeySearch.branchFor sampling.cachedContext) (.call backend.keyName backend.generateKey)) s (KeyBranchResult q) := by
  obtain ⟨⟨original, live, statuses⟩, flag⟩ := h
  have done : ∀ (t : State) (result : Spec.Ffdh.KeySearchResult), ¬keyContinues q →
      KeyDone q.inputs original result t → KeyBranchResult q t := fun _ _ stops finished => by
    simp only [KeyBranchResult, stops, ite_false]; exact ⟨original, _, finished⟩
  unfold VG.Impl.Ffdh.Arm.KeySearch.branchFor
  refine WP.ite (decide (q.keys = 0)) flag ?_ ?_
  · intro zero
    exact WP.mono live.exhausted fun t finished => done t _ (fun c => c.1 (of_decide_eq_true zero)) finished
  intro nonzero
  have keys : q.keys ≠ 0 := of_decide_eq_false nonzero
  refine WP.seq (WP.mono live.scalars_guard fun u ⟨live2, flag2⟩ => ?_)
  refine WP.ite (decide (q.scalars = 0)) (by change some u.z = _; rw [flag2]) ?_ ?_
  · intro zero
    exact WP.mono live2.exhausted fun t finished => done t _ (fun c => c.2.1 (of_decide_eq_true zero)) finished
  intro nonzero2
  have scalars : q.scalars ≠ 0 := of_decide_eq_false nonzero2
  unfold VG.Impl.Ffdh.Arm.KeySearch.attemptOrRequestFor
  refine WP.seq (WP.mono live2.room_guard fun u ⟨live3, flag3⟩ => ?_)
  refine WP.ite _ (by change some u.z = _; rw [flag3]) ?_ ?_
  · intro short
    have less := of_decide_eq_true short
    exact WP.mono live3.request fun t finished => done t _ (fun c => by have := c.2.2.1; omega) finished
  intro enough
  have room : q.used + q.inputs.len ≤ q.inputs.randLen := by
    have := of_decide_eq_false enough; have := live.used_le; omega
  refine WP.seq (WP.mono (attemptRun_ok backend q.inputs original u q.used q.keys q.scalars live3 room)
    fun t ⟨ready, post⟩ => ?_)
  refine WP.mono (classify ready room (Nat.pos_of_ne_zero keys) (Nat.pos_of_ne_zero scalars) post)
    fun t classified => ?_
  have status := attempt_status live statuses keys scalars room
  have remaining : q.inputs.len ≤ (keyRand q.inputs original).length - q.used := by rw [live.rand_length]; omega
  rcases currentStatus_cases q.inputs original q.used with h1 | h2 | h3
  · simp only [KeyClassified, h1, ite_true] at classified
    exact done t _ (fun c => c.2.2.2 (by rw [← status, h1])) classified
  · simp only [KeyClassified, h2, Nat.reduceEqDiff, ite_true, ite_false] at classified
    have continues : keyContinues q := ⟨keys, scalars, by omega, by rw [← status, h2]; decide⟩
    have next : nextKeyPoint q = ⟨q.inputs, q.used + q.inputs.len, q.keys, q.scalars - 1, q.statuses.tail⟩ := by
      simp only [nextKeyPoint, ← status, h2, ite_true]
    simp only [KeyBranchResult, continues, ite_true, next]
    refine ⟨⟨original, classified.1, ?_⟩, classified.2⟩
    rw [← statuses]
    simp only [KeyPublic.tail, keyTail_scalar keys scalars remaining h2, List.tail_cons]
  · simp only [KeyClassified, h3, Nat.reduceEqDiff, ite_false] at classified
    have continues : keyContinues q := ⟨keys, scalars, by omega, by rw [← status, h3]; decide⟩
    have next : nextKeyPoint q = ⟨q.inputs, q.used + q.inputs.len, q.keys - 1, 128, q.statuses.tail⟩ := by
      simp only [nextKeyPoint, ← status, h3, Nat.reduceEqDiff, ite_false]
    simp only [KeyBranchResult, continues, ite_true, next]
    refine ⟨⟨original, classified.1, ?_⟩, classified.2⟩
    rw [← statuses]
    simp only [KeyPublic.tail, keyTail_public keys scalars remaining h3, List.tail_cons]

private theorem leaf {Φ : KeyPoint sampling → State → Prop} {code : Prog isa}
    (get : ∀ q s, Φ q s → KeyAny q.inputs s) (ct : RelCT isa (Two (KeyAny (sampling := sampling))) code (fun _ _ => True)) :
    RelCT isa (Two Φ) code (fun _ _ => True) :=
  ct.mono (fun _ _ ⟨q, h₁, h₂, sp⟩ => ⟨q.inputs, get q _ h₁, get q _ h₂, sp⟩) (fun _ _ h => h)

theorem branch_ct (backend : VG.Proof.Ffdh.Arm.KeyBackend sampling) :
    RelCT isa (Two (KeysGuard (sampling := sampling))) ((VG.Impl.Ffdh.Arm.KeySearch.branchFor sampling.cachedContext) (.call backend.keyName backend.generateKey)) (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.KeySearch.branchFor
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm)
    (leaf (fun _ _ h => h.1.1.any) exhausted_ct) ?_
  refine RelCT.seq (two_piece [.r4] (fun q _ _ h₁ h₂ => key_ctl_pins q _ _ h₁.1.1 h₂.1.1)
    (by taint_decide) scalars_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.trans h₂.2.2.symm)
    (leaf (fun _ _ h => h.1.1.any) exhausted_ct) ?_
  unfold VG.Impl.Ffdh.Arm.KeySearch.attemptOrRequestFor
  refine RelCT.seq (two_piece [.r4] (fun q _ _ h₁ h₂ => key_ctl_pins q _ _ h₁.1.1 h₂.1.1)
    (by taint_decide) room_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm)
    (leaf (fun _ _ h => h.1.1.any) request_ct) ?_
  exact RelCT.seq (two_post ((attempt_run_ct backend).mono
    (fun _ _ ⟨q, h₁, h₂, sp⟩ => ⟨q, attempt_of_room h₁, attempt_of_room h₂, sp⟩) (fun _ _ h => h))
    (fun q s h => attempt_ready backend q s (attempt_of_room h))) classify_ct

end VG.Proof.Ffdh.Arm.KeySearch
