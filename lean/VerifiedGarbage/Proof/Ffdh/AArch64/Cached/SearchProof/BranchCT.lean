module

public import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.AttemptCT
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Loop
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Guards
import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Live
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.AttemptCT
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Loop
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Guards
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Cached.SearchProof.Live
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # An iteration of the key search branches on its public point alone (AArch64)

The attempt's classification branches on its status, the first of the
statuses still to come; the guards on the budgets and the tape, which the
point fixes.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Cached.SearchProof

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.GenerationSearch
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search (ldf stf terminal zeroOut zeroOutputs exhausted advance rejectedScalar rejectedPublic test classify request room entry arguments finish)
open VG.Impl.Ffdh.AArch64.Cached.Search

/-! ## The classification -/

theorem key_attempted_pins : Pins KeyAttempted [.x19] := by
  intro q s t ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.x19.trans h₂.x19.symm

/-- The status in `x9`, compared with `k` in `x10`. -/
def KeyGuard (k : Nat) (q : KeyPoint) (t : State) : Prop :=
  KeyAny q.inputs t ∧ t.gpr .x9 = BitVec.ofNat 64 q.status ∧
    isa.eval (.zero .x .x10) t = some (decide (q.status = k)) ∧ q.status < 4

private theorem first_ready (q : KeyPoint) (s : State) (h : KeyAttempted q s) :
    WP isa (.block (advance ++ test 1)) s (KeyGuard 1 q) := by
  obtain ⟨original, h, hst, hk, hs, hr, hp⟩ := h
  have he := attempt_status h hst hk hs hr
  have h4 : q.status < 4 := by
    rw [← he]
    rcases attemptStatus_cases (policy:=.cached) q.inputs.a q.inputs.len ((keyRand original).drop q.used) with
      h | h | h <;> omega
  refine WP.mono (key_classify_head h hr hp) fun t ⟨ht, _, hax, hev⟩ => ?_
  exact ⟨⟨original, _, _, _, ht⟩, by rw [hax, he], by rw [hev, he], h4⟩

private theorem next_ready (j k : Nat) (hk : k = 1 ∨ k = 2 ∨ k = 3) (q : KeyPoint) (s : State)
    (h : KeyGuard j q s ∧ isa.eval (.zero .x .x10) s = some false) :
    WP isa (.block (test k)) s (KeyGuard k q) := by
  obtain ⟨⟨⟨o, u, a, c, hl⟩, ha, _, h4⟩, _⟩ := h
  refine WP.mono (test_ok ha h4 hk) fun t ⟨⟨he, hm⟩, kt⟩ => ?_
  exact ⟨⟨o, u, a, c, hl.keep kt hm⟩, (kt.gpr .x9 (by decide)).trans ha, he, h4⟩

private theorem leaf {k : Nat} {b : Bool} {c : Prog isa} (hc : RelCT isa (Two KeyAny) c fun _ _ => True) :
    RelCT isa (Two fun q s => KeyGuard k q s ∧ isa.eval (.zero .x .x10) s = some b) c fun _ _ => True :=
  hc.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q.inputs, h₁.1.1, h₂.1.1, hsp⟩) fun _ _ h => h

private theorem guard_eq (k : Nat) (q : KeyPoint) (s₁ s₂ : State) (h₁ : KeyGuard k q s₁)
    (h₂ : KeyGuard k q s₂) : isa.eval (.zero .x .x10) s₁ = isa.eval (.zero .x .x10) s₂ :=
  h₁.2.2.1.trans h₂.2.2.1.symm

private theorem no_pins {Φ : KeyPoint → State → Prop} : Pins Φ [] := fun _ _ _ _ _ _ h => by cases h

theorem key_classify_ct : RelCT isa (Two KeyAttempted) classify (fun _ _ => True) := by
  unfold classify
  refine RelCT.seq (two_piece [.x19] key_attempted_pins (by taint_decide) first_ready) ?_
  refine two_ite (guard_eq 1) (leaf key_accepted_ct) ?_
  refine RelCT.seq (two_post (two_taint [] no_pins (by taint_decide))
    (next_ready 1 2 (.inr (.inl rfl)))) ?_
  refine two_ite (guard_eq 2) (leaf key_rejected_scalar_ct) ?_
  refine RelCT.seq (two_post (two_taint [] no_pins (by taint_decide))
    (next_ready 2 3 (.inr (.inr rfl)))) ?_
  exact two_ite (guard_eq 3) (leaf key_rejected_public_ct) (leaf key_exhausted_ct)

/-! ## The guards -/

/-- Whether the search goes on after an iteration from `q`: it attempts, and
the attempt is rejected. -/
def keyContinues (q : KeyPoint) : Prop :=
  q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.inputs.len ≤ q.inputs.randLen - q.used ∧ q.status ≠ 1

instance (q : KeyPoint) : Decidable (keyContinues q) := inferInstanceAs
  (Decidable (q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.inputs.len ≤ q.inputs.randLen - q.used ∧ q.status ≠ 1))

/-- The point after a rejected attempt. -/
def nextKeyPoint (q : KeyPoint) : KeyPoint :=
  if q.status = 2 then ⟨q.inputs, q.used + q.inputs.len, q.keys, q.scalars - 1, q.statuses.tail⟩
  else ⟨q.inputs, q.used + q.inputs.len, q.keys - 1, 128, q.statuses.tail⟩

theorem nextKeyPoint_inputs (q : KeyPoint) : (nextKeyPoint q).inputs = q.inputs := by
  unfold nextKeyPoint; split <;> rfl

theorem nextKeyPoint_measure {q : KeyPoint} (h : keyContinues q) :
    128 * (nextKeyPoint q).keys + (nextKeyPoint q).scalars < 128 * q.keys + q.scalars := by
  obtain ⟨hk, hs, -, -⟩ := h
  unfold nextKeyPoint; split <;> dsimp only <;> omega

/-- After the guards, the attempt and its classification. -/
def KeyBranchResult (q : KeyPoint) (t : State) : Prop :=
  if keyContinues q then KeyCTL (nextKeyPoint q) t ∧ word t.mem q.inputs.control 112 = 4
  else ∃ original r, KeyDone q.inputs original r t

theorem branch_x19 {q : KeyPoint} {t : State} (h : KeyBranchResult q t) :
    t.gpr .x19 = q.inputs.control := by
  by_cases hc : keyContinues q
  · simp only [KeyBranchResult, hc, ite_true] at h
    obtain ⟨⟨_, hl, _⟩, _⟩ := h
    rw [hl.x19, nextKeyPoint_inputs]
  · simp only [KeyBranchResult, hc, ite_false] at h
    obtain ⟨_, _, hd⟩ := h
    exact hd.x19

def KeysGuard (q : KeyPoint) (s : State) : Prop :=
  KeyCTL q s ∧ isa.eval (.zero .x .x9) s = some (decide (q.keys = 0))

def ScalarsGuard (q : KeyPoint) (s : State) : Prop :=
  KeyCTL q s ∧ q.keys ≠ 0 ∧ isa.eval (.zero .x .x9) s = some (decide (q.scalars = 0))

def RoomGuard (q : KeyPoint) (s : State) : Prop :=
  KeyCTL q s ∧ q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧
    isa.eval (.zero .x .x12) s = some (decide (q.inputs.randLen - q.used < q.inputs.len))

theorem keys_ready (q : KeyPoint) (s : State) (h : KeyCTL q s) :
    WP isa (.block [ldf .x9 0]) s (KeysGuard q) := by
  obtain ⟨original, h, hst⟩ := h
  exact WP.mono (keys_guard h) fun _ ⟨ht, he⟩ => ⟨⟨original, ht, hst⟩, he⟩

theorem scalars_ready (q : KeyPoint) (s : State) (h : KeysGuard q s ∧ isa.eval (.zero .x .x9) s = some false) :
    WP isa (.block [ldf .x9 1]) s (ScalarsGuard q) := by
  obtain ⟨⟨⟨original, h, hst⟩, he⟩, hf⟩ := h
  have hk : q.keys ≠ 0 := of_decide_eq_false (Option.some.inj (he.symm.trans hf))
  exact WP.mono (scalars_guard h) fun _ ⟨ht, he⟩ => ⟨⟨original, ht, hst⟩, hk, he⟩

theorem room_ready (q : KeyPoint) (s : State) (h : ScalarsGuard q s ∧ isa.eval (.zero .x .x9) s = some false) :
    WP isa (.block room) s (RoomGuard q) := by
  obtain ⟨⟨⟨original, h, hst⟩, hk, he⟩, hf⟩ := h
  have hs : q.scalars ≠ 0 := of_decide_eq_false (Option.some.inj (he.symm.trans hf))
  exact WP.mono (room_guard h) fun _ ⟨ht, he⟩ => ⟨⟨original, ht, hst⟩, hk, hs, he⟩

theorem attempt_of_room {q : KeyPoint} {s : State}
    (h : RoomGuard q s ∧ isa.eval (.zero .x .x12) s = some false) : KeyReady q s := by
  obtain ⟨⟨⟨original, hl, hst⟩, hk, hs, he⟩, hf⟩ := h
  have hr := of_decide_eq_false (Option.some.inj (he.symm.trans hf))
  exact ⟨⟨original, hl, hst⟩, hk, hs, by have := hl.used_le; omega⟩

theorem key_branch_ready (a : Attempt) (q : KeyPoint) (s : State) (h : KeysGuard q s) :
    WP isa (branch a.call) s (KeyBranchResult q) := by
  obtain ⟨⟨original, hl, hst⟩, he⟩ := h
  have done : ∀ (t : State) (r : Spec.Ffdh.KeySearchResult), ¬keyContinues q →
      KeyDone q.inputs original r t → KeyBranchResult q t := fun t r hn hd => by
    simp only [KeyBranchResult, hn, ite_false]; exact ⟨original, r, hd⟩
  unfold branch
  refine WP.ite (decide (q.keys = 0)) he ?_ ?_
  · intro hz
    exact WP.mono (key_exhausted hl) fun t ht => done t _ (fun hc => hc.1 (of_decide_eq_true hz)) ht
  intro hnz
  have hk : q.keys ≠ 0 := of_decide_eq_false hnz
  refine WP.seq (WP.mono (scalars_guard hl) fun u ⟨hu, he2⟩ => ?_)
  refine WP.ite (decide (q.scalars = 0)) he2 ?_ ?_
  · intro hz
    exact WP.mono (key_exhausted hu) fun t ht => done t _ (fun hc => hc.2.1 (of_decide_eq_true hz)) ht
  intro hnz2
  have hs : q.scalars ≠ 0 := of_decide_eq_false hnz2
  unfold attemptOrRequest
  refine WP.seq (WP.mono (room_guard hu) fun u ⟨hu3, hb⟩ => ?_)
  refine WP.ite _ hb ?_ ?_
  · intro hshort
    have := of_decide_eq_true hshort
    exact WP.mono (key_request hu3) fun t ht => done t _ (fun hc => by have := hc.2.2.1; omega) ht
  intro hlong
  have hroom : q.used + q.inputs.len ≤ q.inputs.randLen := by
    have := of_decide_eq_false hlong; have := hl.used_le; omega
  refine WP.seq (WP.mono (key_attempt_run a hu3 hroom) fun t ⟨ht, hp⟩ => ?_)
  refine WP.mono (key_classify ht hroom (Nat.pos_of_ne_zero hk) (Nat.pos_of_ne_zero hs) hp)
    fun r hq => ?_
  have hstat := attempt_status hl hst hk hs hroom
  have hr : q.inputs.len ≤ (keyRand original).length - q.used := by rw [hl.rand_length]; omega
  rcases attemptStatus_cases (policy:=.cached) q.inputs.a q.inputs.len ((keyRand original).drop q.used) with h1 | h2 | h3
  · simp only [KeyClassified, h1, ite_true] at hq
    exact done r _ (fun hc => hc.2.2.2 (by rw [← hstat, h1])) hq
  · simp only [KeyClassified, h2, Nat.reduceEqDiff, ite_true, ite_false] at hq
    have hc : keyContinues q := ⟨hk, hs, by omega, by rw [← hstat, h2]; decide⟩
    have hn : nextKeyPoint q = ⟨q.inputs, q.used + q.inputs.len, q.keys, q.scalars - 1, q.statuses.tail⟩ := by
      simp only [nextKeyPoint, ← hstat, h2, ite_true]
    simp only [KeyBranchResult, hc, ite_true, hn]
    refine ⟨⟨original, hq.1, ?_⟩, hq.2⟩
    rw [← hst]
    simp only [KeyPublic.tail, keyTail_scalar hk hs hr h2, List.tail_cons]
  · simp only [KeyClassified, h3, Nat.reduceEqDiff, ite_false] at hq
    have hc : keyContinues q := ⟨hk, hs, by omega, by rw [← hstat, h3]; decide⟩
    have hn : nextKeyPoint q = ⟨q.inputs, q.used + q.inputs.len, q.keys - 1, 128, q.statuses.tail⟩ := by
      simp only [nextKeyPoint, ← hstat, h3, Nat.reduceEqDiff, ite_false]
    simp only [KeyBranchResult, hc, ite_true, hn]
    refine ⟨⟨original, hq.1, ?_⟩, hq.2⟩
    rw [← hst]
    simp only [KeyPublic.tail, keyTail_public hk hs hr h3, List.tail_cons]

private theorem leafB {Φ : KeyPoint → State → Prop} {c : Prog isa}
    (hΦ : ∀ q s, Φ q s → KeyAny q.inputs s) (hc : RelCT isa (Two KeyAny) c fun _ _ => True) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  hc.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q.inputs, hΦ q _ h₁, hΦ q _ h₂, hsp⟩) fun _ _ h => h

theorem key_branch_ct (a : Attempt) :
    RelCT isa (Two KeysGuard) (branch a.call) (fun _ _ => True) := by
  unfold branch
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm)
    (leafB (fun _ _ h => h.1.1.any) key_exhausted_ct) ?_
  refine RelCT.seq (two_piece [.x19] (fun q _ _ h₁ h₂ => key_ctl_pins q _ _ h₁.1.1 h₂.1.1)
    (by taint_decide) scalars_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.trans h₂.2.2.symm)
    (leafB (fun _ _ h => h.1.1.any) key_exhausted_ct) ?_
  unfold attemptOrRequest
  refine RelCT.seq (two_piece [.x19] (fun q _ _ h₁ h₂ => key_ctl_pins q _ _ h₁.1.1 h₂.1.1)
    (by taint_decide) room_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm)
    (leafB (fun _ _ h => h.1.1.any) key_request_ct) ?_
  exact RelCT.seq (two_post ((key_attempt_run_ct a).mono
      (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, attempt_of_room h₁, attempt_of_room h₂, hsp⟩) fun _ _ h => h)
    fun q s h => key_attempt_ready a q s (attempt_of_room h)) key_classify_ct

end VG.Proof.Ffdh.AArch64.Cached.SearchProof
