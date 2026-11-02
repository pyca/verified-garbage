module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.LeafCT
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Classify
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTBase
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Loop
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Contract
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.LeafCT
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Classify
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.ParameterCandidate.CTBase
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Loop
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ffdh.Contract

/-! # The parameter search's timing depends on its public data alone (PPC64LE)

Every branch is on the attempts left, the candidate's status and the
tape's length, which the point (the public descriptor, the octets consumed
and the attempts left) fixes.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Spec.Ffdh
open VG.PPC64LE.Taint
open VG.Proof.Ffdh.PPC64LE.ParameterCandidate (two_ite)
open VG.Proof.Ffdh.Control (writeController)
open VG.Impl.Ffdh.PPC64LE.Generation.Search

/-! ## The classification -/

theorem s_candidated_pins : Pins SCandidated [.r31] := by
  intro q s t ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.r31.trans h₂.r31.symm

/-- The candidate's status. -/
abbrev SPoint.status (q : SPoint) : Nat := candidateStatus (q.inputs.cand q.used)

/-- The status in `r9`, compared with `j` in `r12`. -/
def SGuard (j : Nat) (q : SPoint) (t : State) : Prop :=
  SCTL q t ∧ q.k ≠ 0 ∧ t.gpr .r9 = BitVec.ofNat 64 q.status ∧
    isa.eval (.zero .d .r12) t = some (decide (q.status = j))

/-- After the status and the pointer to `used` are loaded. -/
def SHead (q : SPoint) (t : State) : Prop :=
  SCandidated q t ∧ t.gpr .r11 = q.inputs.up ∧ t.gpr .r9 = BitVec.ofNat 64 q.status

private theorem head_first (q : SPoint) (s : State) (h : SCandidated q s) :
    WP isa (.block [.lsl .r9 .r3 32, .lsr .d .r9 .r9 32, ldf .r11 7]) s (SHead q) := by
  obtain ⟨original, h, hk, hp⟩ := h
  have a := h.access
  have hv7 := h.header (j := 7) (v := q.inputs.up) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv7
  have h9 := low32 hp.1
  refine WP.mono (WP.keep [.r9, .r11] (Q := fun t =>
    (t.gpr .r11 = q.inputs.up ∧ t.gpr .r9 = BitVec.ofNat 64 q.status) ∧ t.mem = s.mem) ?_
    (by decide)) fun t ⟨⟨⟨h11, h9⟩, hm⟩, k⟩ => ?_
  · prun [ldf, h.r31, hv7, a.ld 56 (by decide), h9]
  · refine ⟨⟨original, h.keep k hm, hk, ?_⟩, h11, h9⟩
    unfold CandPost at hp ⊢
    rw [hm, k.gpr .r3 (by decide)]
    exact hp

theorem s_head_pins : Pins SHead [.r11] := by
  intro q s t h₁ h₂ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.2.1.trans h₂.2.1.symm

private theorem head_second (q : SPoint) (s : State) (h : SHead q s) :
    WP isa (.block [.load .d .r10 .r11 0, .subi .r12 .r9 1]) s (SGuard 1 q) := by
  obtain ⟨⟨original, h, hk, _⟩, h11, h9⟩ := h
  have hu : InRegions (s.rd ++ s.wr) (q.inputs.up + BitVec.ofNat 64 0) 8 := by
    refine ⟨⟨q.inputs.up, 8⟩, List.mem_append_right _ ?_, ?_⟩
    · rw [h.wr, h.input.1.2.2.2.1, ← h.input.used_eq]; simp [inWrites]
    · exact Offset.contains_base q.inputs.up (d := 0) (n := 8) (k := 8) (by decide) (by decide)
  have hst : q.status < 3 := status_lt (q.inputs.cand q.used)
  refine WP.mono (WP.keep [.r10, .r12] (Q := fun t =>
    isa.eval (.zero .d .r12) t = some (decide (q.status = 1)) ∧ t.mem = s.mem) ?_
    (by decide)) fun t ⟨⟨he, hm⟩, k⟩ =>
      ⟨⟨original, h.keep k hm⟩, hk, (k.gpr .r9 (by decide)).trans h9, he⟩
  prun [h11, h9, hu]
  have : ∀ st < 3, ((BitVec.ofNat 64 st - BitVec.ofNat 64 1) == 0) = decide (st = 1) := by decide
  refine (eval_zero _ _).trans ?_
  rw [RegUpd.gpr_write_self, this _ hst]

private theorem second_ready (q : SPoint) (s : State)
    (h : SGuard 1 q s ∧ isa.eval (.zero .d .r12) s = some false) :
    WP isa (.block [.subi .r12 .r9 2]) s (SGuard 2 q) := by
  obtain ⟨⟨⟨o, hl⟩, hk, h9, _⟩, _⟩ := h
  refine WP.mono (test_two h9 (status_lt _)) fun t ⟨⟨he, hm⟩, kt⟩ => ?_
  exact ⟨⟨o, hl.keep kt hm⟩, hk, (kt.gpr .r9 (by decide)).trans h9, he⟩

private theorem guard_eq (j : Nat) (q : SPoint) (s₁ s₂ : State) (h₁ : SGuard j q s₁)
    (h₂ : SGuard j q s₂) : isa.eval (.zero .d .r12) s₁ = isa.eval (.zero .d .r12) s₂ :=
  h₁.2.2.2.trans h₂.2.2.2.symm

private theorem leafB {α : Type} {Φ : α → State → Prop} {c : Prog isa} (f : α → SPub)
    (hΦ : ∀ q s, Φ q s → SAny (f q) s) (hc : RelCT isa (Two SAny) c fun _ _ => True) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  hc.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨f q, hΦ q _ h₁, hΦ q _ h₂, hsp⟩) fun _ _ h => h

/-- Whether the tape holds the entropy cap, after a short tape. -/
def SShort (q : SPoint) (t : State) : Prop :=
  SCTL q t ∧ isa.eval (.zero .d .r5) t =
    some (decide (parameterEntropy q.inputs.bits ≤ q.inputs.randLen - q.used))

private theorem short_ready (q : SPoint) (s : State)
    (h : SGuard 2 q s ∧ isa.eval (.zero .d .r12) s = some false) :
    WP isa (.block [ldf .r3 11, ldf .r4 2, .sub .r5 .r3 .r4, .lsr .d .r5 .r5 63]) s (SShort q) := by
  obtain ⟨⟨⟨o, hl⟩, _⟩, _⟩ := h
  exact WP.mono (short_guard hl) fun t ⟨⟨ht, _⟩, he⟩ => ⟨⟨o, ht⟩, he⟩

theorem s_short_ct : RelCT isa (Two fun q s => SGuard 2 q s ∧ isa.eval (.zero .d .r12) s = some false)
    short (fun _ _ => True) := by
  unfold short
  refine RelCT.seq (two_post (two_taint [.r31] (fun q _ _ h₁ h₂ => s_ctl_pins q _ _ h₁.1.1 h₂.1.1)
    (by taint_decide)) short_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · exact leafB SPoint.inputs (fun _ _ h => h.1.1.any) s_exhausted_ct
  · exact leafB SPoint.inputs (fun _ _ h => h.1.1.any) s_request_ct

theorem s_classify_ct : RelCT isa (Two SCandidated) classify (fun _ _ => True) := by
  unfold classify
  change RelCT isa (Two SCandidated) (.seq (.block ([.lsl .r9 .r3 32, .lsr .d .r9 .r9 32, ldf .r11 7] ++
    [.load .d .r10 .r11 0, .subi .r12 .r9 1])) _) _
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    (two_post (two_taint [.r31] s_candidated_pins (by taint_decide)) head_first)
    (two_post (two_taint [.r11] s_head_pins (by taint_decide)) head_second))) ?_
  refine two_ite (guard_eq 1) (leafB SPoint.inputs (fun _ _ h => h.1.1.any) s_accept_ct) ?_
  refine RelCT.seq (two_post (two_taint [] no_pins (by taint_decide)) second_ready) ?_
  exact two_ite (guard_eq 2) (leafB SPoint.inputs (fun _ _ h => h.1.1.any) s_reject_ct) s_short_ct

/-! ## An iteration -/

/-- Whether the search goes on after an iteration from `q`: a candidate is
rejected. -/
def sContinues (q : SPoint) : Prop := q.k ≠ 0 ∧ q.status = 2

instance (q : SPoint) : Decidable (sContinues q) :=
  inferInstanceAs (Decidable (q.k ≠ 0 ∧ q.status = 2))

/-- The point after a rejected candidate. -/
def nextPoint (q : SPoint) : SPoint := ⟨q.inputs, q.used + q.inputs.read q.used, q.k - 1⟩

/-- After the test of the attempts, the candidate and its classification. -/
def SBranchResult (q : SPoint) (t : State) : Prop :=
  if sContinues q then SCTL (nextPoint q) t ∧ word t.mem q.inputs.control 112 = 4
  else ∃ original r, SDone q.inputs original r t

theorem branch_r31 {q : SPoint} {t : State} (h : SBranchResult q t) :
    t.gpr .r31 = q.inputs.control := by
  by_cases hc : sContinues q
  · simp only [SBranchResult, hc, ite_true] at h
    obtain ⟨⟨_, hl⟩, _⟩ := h
    exact hl.r31
  · simp only [SBranchResult, hc, ite_false] at h
    obtain ⟨_, _, hd⟩ := h
    exact hd.r31

def KGuard (q : SPoint) (s : State) : Prop :=
  SCTL q s ∧ isa.eval (.zero .d .r9) s = some (decide (q.k = 0))

theorem k_ready (q : SPoint) (s : State) (h : SCTL q s) :
    WP isa (.block [ldf .r9 0]) s (KGuard q) := by
  obtain ⟨original, h⟩ := h
  exact WP.mono (attempts_guard h) fun _ ⟨ht, he⟩ => ⟨⟨original, ht⟩, he⟩

/-- The branch of an iteration. -/
abbrev sBranch (c : Cand) : Prog isa := .ite (.zero .d .r9) exhausted (.seq (candidateRun c.call) classify)

theorem s_branch_ready (c : Cand) (q : SPoint) (s : State) (h : KGuard q s) :
    WP isa (sBranch c) s (SBranchResult q) := by
  obtain ⟨⟨original, hl⟩, he⟩ := h
  refine WP.ite (decide (q.k = 0)) he ?_ ?_
  · intro hz
    have hz' := of_decide_eq_true hz
    refine WP.mono (search_exhausted hl) fun t ht => ?_
    simp only [SBranchResult, sContinues, hz', ne_eq, not_true_eq_false, false_and, ite_false]
    exact ⟨original, _, ht⟩
  intro hnz
  have hk : q.k ≠ 0 := of_decide_eq_false hnz
  refine WP.seq (WP.mono (search_candidate_run c hl) fun t ⟨ht, hp⟩ => ?_)
  refine WP.mono (search_classify ht hk hp) fun r hr => ?_
  unfold SClassified at hr
  by_cases h2 : q.status = 2
  · simp only [SPoint.status] at h2
    simp only [h2, ite_true] at hr
    have hc : sContinues q := ⟨hk, h2⟩
    simp only [SBranchResult, hc, ite_true]
    exact ⟨⟨original, hr.1⟩, hr.2⟩
  · simp only [SPoint.status] at h2
    simp only [h2, ite_false] at hr
    have hc : ¬sContinues q := fun hc => h2 hc.2
    simp only [SBranchResult, hc, ite_false]
    exact ⟨original, _, hr⟩

theorem s_branch_ct (c : Cand) : RelCT isa (Two KGuard) (sBranch c) (fun _ _ => True) := by
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm)
    (leafB SPoint.inputs (fun _ _ h => h.1.1.any) s_exhausted_ct) ?_
  have hr : ∀ q s, KGuard q s ∧ isa.eval (.zero .d .r9) s = some false → SReady q s :=
    fun q s ⟨⟨hl, he⟩, hf⟩ => ⟨hl, of_decide_eq_false (Option.some.inj (he.symm.trans hf))⟩
  exact RelCT.seq (two_post ((s_candidate_run_ct c).mono
      (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, hr q _ h₁, hr q _ h₂, hsp⟩) fun _ _ h => h)
    fun q s h => s_candidate_ready c q s (hr q s h)) s_classify_ct

theorem s_iteration_ct (c : Cand) :
    RelCT isa (Two SCTL) (iteration c.call) (fun _ _ => True) := by
  unfold iteration
  refine RelCT.seq (two_post (two_taint [.r31] s_ctl_pins (by taint_decide)) k_ready) ?_
  exact RelCT.seq (two_post (s_branch_ct c) (s_branch_ready c))
    (two_taint [.r31] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact (branch_r31 h₁).trans (branch_r31 h₂).symm) (by taint_decide))

def SCTStep (q : SPoint) (s : State) : Prop :=
  if sContinues q then isa.eval (.zero .d .r9) s = some true ∧ SCTL (nextPoint q) s
  else isa.eval (.zero .d .r9) s = some false

theorem s_ct_step (c : Cand) (q : SPoint) (s : State) (h : SCTL q s) :
    WP isa (iteration c.call) s (SCTStep q) := by
  unfold iteration
  refine WP.seq (WP.mono (k_ready q s h) fun u hu => ?_)
  refine WP.seq (WP.mono (s_branch_ready c q u hu) fun t ht => ?_)
  by_cases hc : sContinues q
  · simp only [SBranchResult, hc, ite_true] at ht
    obtain ⟨⟨original, hl⟩, hw⟩ := ht
    refine WP.mono (live_loop_guard hl hw) fun z ⟨hz, hzl⟩ => ?_
    simp only [SCTStep, hc, ite_true]
    exact ⟨hz, original, hzl⟩
  · simp only [SBranchResult, hc, ite_false] at ht
    obtain ⟨_, _, hd⟩ := ht
    refine WP.mono (done_loop_guard hd) fun z ⟨hz, _⟩ => ?_
    simp only [SCTStep, hc, ite_false]
    exact hz

private def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ q, n = q.k + 1 ∧ SCTL q s ∧ SCTL q t ∧ s.sp = t.sp

private theorem iteration_pair (c : Cand) (n : Nat) :
    RelCT isa (LoopPair n) (iteration c.call) fun s t =>
      isa.eval (.zero .d .r9) s = isa.eval (.zero .d .r9) t ∧
      (isa.eval (.zero .d .r9) s = some false → True) ∧
      (isa.eval (.zero .d .r9) s = some true → ∃ m < n, LoopPair m s t) := by
  have hw (q : SPoint) (s : State) (h : n = q.k + 1 ∧ SCTL q s) :
      WP isa (iteration c.call) s fun t => n = q.k + 1 ∧ SCTStep q t :=
    WP.mono (s_ct_step c q s h.2) fun _ ht => ⟨h.1, ht⟩
  have hc := two_post ((s_iteration_ct c).mono
    (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, h₁.2, h₂.2, hsp⟩) (fun _ _ h => h)) hw
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂, hsp⟩ => ⟨q, ⟨hn, h₁⟩, ⟨hn, h₂⟩, hsp⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, ⟨_, h₂⟩, hsp⟩
  by_cases hb : sContinues q
  · simp only [SCTStep, hb, ite_true] at h₁ h₂
    refine ⟨h₁.1.trans h₂.1.symm, fun _ => trivial, fun _ => ?_⟩
    refine ⟨(nextPoint q).k + 1, ?_, nextPoint q, rfl, h₁.2, h₂.2, hsp⟩
    have := hb.1
    simp only [nextPoint]
    omega
  · simp only [SCTStep, hb, ite_false] at h₁ h₂
    exact ⟨h₁.trans h₂.symm, fun _ => trivial, fun ht => absurd (ht.symm.trans h₁) (by decide)⟩

theorem s_loop_ct (c : Cand) :
    RelCT isa (Two SCTL) (.loop (iteration c.call) (.zero .d .r9)) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht, hsp⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration c.call) (c := .zero .d .r9)
    (Q := fun _ _ => True) LoopPair (iteration_pair c) (q.k + 1)
    _ _ _ _ _ _ ⟨q, rfl, hs, ht, hsp⟩ he₁ he₂

end VG.Proof.Ffdh.PPC64LE.Generation
