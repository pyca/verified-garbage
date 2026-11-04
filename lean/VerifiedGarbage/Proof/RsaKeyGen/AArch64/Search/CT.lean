module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.LeafCT
public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Loop
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.LeafCT
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Loop
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Base
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! # The RSA prime search's timing: the classification and the loop (AArch64)

Each branch the search takes is a function of the point: of the status and
consumption the trace gives the candidate, of the counted candidates left
and of the octets left on the tape.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Search

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep eval_zero)
open VG.Impl.RsaKeyGen.AArch64.Search
open VG.Spec.RsaKeyGen (primeEntropy PrimeSearchResult)

/-! ## The classification -/

theorem s_candidated_pins : Pins SCandidated [.x19] := by
  intro q s t ⟨_, h₁, _⟩ ⟨_, h₂, _⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.x19.trans h₂.x19.symm

theorem SCandidated.status {q : SPoint} {t : State} (h : SCandidated q t) :
    ((t.gpr .x0).setWidth 32).toNat = q.status := by
  obtain ⟨o, hl, ht, hk, hp⟩ := h
  rw [hp.1, ← SCTL.status_eq ht hk]

theorem SPoint.status_lt (q : SPoint) {t : State} (h : SCandidated q t) : q.status < 4 := by
  obtain ⟨o, hl, ht, hk, hp⟩ := h
  rw [← SCTL.status_eq ht hk]; exact VG.Proof.RsaKeyGen.AArch64.Search.status_lt _

theorem SPoint.cand_lt (q : SPoint) {t : State} (h : SCandidated q t) : q.cand < 2 ^ 64 := by
  obtain ⟨o, hl, ht, hk, hp⟩ := h
  rw [← SCTL.cand_eq hl ht hk]
  have := candUsed_le (p := q.inputs) (original := o) q.used
  have : q.inputs.randLen < 2 ^ 64 := by rw [← hl.input.2]; exact BitVec.isLt _
  omega

/-- After the status and the pointer to `used` are loaded. -/
def SHead (q : SPoint) (t : State) : Prop :=
  SCandidated q t ∧ t.gpr .x11 = q.inputs.up ∧ t.gpr .x9 = BitVec.ofNat 64 q.status

private theorem head_first (q : SPoint) (s : State) (h : SCandidated q s) :
    WP isa (.block [.addImm .w .x9 .x0 0, ldf .x11 7]) s (SHead q) := by
  have hst := q.status_lt h
  have hs := h.status
  obtain ⟨original, hl, ht, hk, hp⟩ := h
  have a := hl.access
  have hv7 := hl.header (j := 7) (v := q.inputs.up) (by simp [SPub.headers])
  simp only [Bignum.word, off, Nat.reduceMul] at hv7
  have h0 : (s.gpr .x0).setWidth 32 = BitVec.ofNat 32 q.status := by
    apply BitVec.eq_of_toNat_eq
    rw [hs, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine WP.mono (WP.keep [.x9, .x11] (Q := fun t =>
    (t.gpr .x11 = q.inputs.up ∧ t.gpr .x9 = BitVec.ofNat 64 q.status) ∧ t.mem = s.mem) ?_
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨⟨h11, h9⟩, hm⟩, k⟩ => ?_
  · brun [ldf, hl.x19, hv7, a.ld 56 (by decide),
      VG.Proof.RsaKeyGen.AArch64.exec_addImm_w (show 0 < 4096 by decide), h0]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · exact ⟨⟨original, hl.keep k hm, ht, hk, hp.keep hm (by rw [k.gpr .x0 (by decide)])⟩, h11, h9⟩

theorem s_head_pins : Pins SHead [.x11] := by
  intro q s t h₁ h₂ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.2.1.trans h₂.2.1.symm

/-- The status in `x9` and the octets read in `x10`, with the status
compared with 1 in `x12`. -/
def SGuard (q : SPoint) (t : State) : Prop :=
  SCandidated q t ∧ t.gpr .x9 = BitVec.ofNat 64 q.status ∧ t.gpr .x10 = BitVec.ofNat 64 q.cand ∧
    isa.eval (.zero .x .x12) t = some (decide (q.status = 1))

private theorem head_second (q : SPoint) (s : State) (h : SHead q s) :
    WP isa (.block [Impl.Bignum.AArch64.ld .x10 .x11, .subImm .x .x12 .x9 1]) s (SGuard q) := by
  have hst := q.status_lt h.1
  obtain ⟨⟨original, hl, ht, hk, hp⟩, h11, h9⟩ := h
  have hu : InRegions (s.rd ++ s.wr) q.inputs.up 8 := by
    refine ⟨⟨q.inputs.up, 8⟩, List.mem_append_right _ ?_, ?_⟩
    · rw [hl.wr, hl.input.1.2.2.2.1, ← hl.input.used_eq]; simp [inWrites]
    · simpa only [BitVec.add_zero] using Offset.contains_base q.inputs.up (d := 0) (n := 8) (k := 8)
        (by decide) (by decide)
  have hw : s.mem.readW q.inputs.up 64 = BitVec.ofNat 64 q.cand := by
    have := hp.2.2
    change [word s.mem q.inputs.up 0] = _ at this
    simp only [Bignum.word, off, BitVec.add_zero, List.cons.injEq, and_true] at this
    rw [this, ← SCTL.cand_eq hl ht hk]; rfl
  refine WP.mono (WP.keep [.x10, .x12] (Q := fun t =>
    (t.gpr .x10 = BitVec.ofNat 64 q.cand ∧ isa.eval (.zero .x .x12) t = some (decide (q.status = 1))) ∧
      t.mem = s.mem) ?_
    (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨⟨h10, he⟩, hm⟩, k⟩ =>
      ⟨⟨original, hl.keep k hm, ht, hk, hp.keep hm (by rw [k.gpr .x0 (by decide)])⟩,
        (k.gpr .x9 (by decide)).trans h9, h10, he⟩
  brun [h11, h9, hu, hw]
  have : ∀ st < 4, ((BitVec.ofNat 64 st - BitVec.ofNat 64 1) == 0) = decide (st = 1) := by decide
  simp only [eval, State.read, RegUpd.gpr_write, ite_true, Size.bits, BitVec.setWidth_eq, this _ hst]

private theorem leafB {α : Type} {Φ : α → State → Prop} {c : Prog isa} (f : α → SPub)
    (hΦ : ∀ q s, Φ q s → SAny (f q) s) (hc : RelCT isa (Two SAny) c fun _ _ => True) :
    RelCT isa (Two Φ) c fun _ _ => True :=
  hc.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨f q, hΦ q _ h₁, hΦ q _ h₂, hsp⟩) fun _ _ h => h

theorem SCandidated.any {q : SPoint} {t : State} (h : SCandidated q t) : SAny q.inputs t :=
  let ⟨o, hl, _⟩ := h; ⟨o, _, _, hl⟩

/-- Whether the tape holds the entropy budget, after a short tape. -/
def SShort (q : SPoint) (t : State) : Prop :=
  SAny q.inputs t ∧ isa.eval (.zero .x .x12) t =
    some (decide (q.inputs.randLen - q.used < primeEntropy q.inputs.len))

private theorem short_ready (q : SPoint) (s : State) (h : SGuard q s ∧ isa.eval (.zero .x .x12) s = some false) :
    WP isa (.block [ldf .x10 11, ldf .x11 2, .subs .x .x12 .x10 .x11, Impl.Bignum.AArch64.movi .x13 0,
      Impl.Bignum.AArch64.movi .x14 1, .csel .x .x12 .x14 .x13]) s (SShort q) := by
  obtain ⟨⟨⟨o, hl, _⟩, _⟩, _⟩ := h
  exact WP.mono (short_guard hl) fun t ⟨⟨ht, _⟩, he⟩ => ⟨⟨o, _, _, ht⟩, he⟩

theorem s_short_ct : RelCT isa (Two fun q s => SGuard q s ∧ isa.eval (.zero .x .x12) s = some false)
    short (fun _ _ => True) := by
  unfold short
  refine RelCT.seq (two_piece [.x19] (fun q _ _ h₁ h₂ => s_candidated_pins q _ _ h₁.1.1 h₂.1.1)
    (by taint_decide) short_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · exact leafB SPoint.inputs (fun _ _ h => h.1.1) s_request_ct
  · exact leafB SPoint.inputs (fun _ _ h => h.1.1) s_exhausted_ct

/-- The guard of a rejected candidate's progress check. -/
theorem s_rejected_ct :
    RelCT isa (Two fun q s => SGuard q s ∧ isa.eval (.zero .x .x12) s = some false)
      rejected (fun _ _ => True) := by
  unfold rejected
  refine two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.1.2.2.1, h₂.1.2.2.1])
    (leafB SPoint.inputs (fun _ _ h => h.1.1.1.any) s_exhausted_ct)
    (leafB SPoint.inputs (fun _ _ h => h.1.1.1.any) s_reject_ct)

theorem s_classify_ct : RelCT isa (Two SCandidated) classify (fun _ _ => True) := by
  unfold classify
  change RelCT isa (Two SCandidated) (.seq (.block ([.addImm .w .x9 .x0 0, ldf .x11 7] ++
    [Impl.Bignum.AArch64.ld .x10 .x11, .subImm .x .x12 .x9 1])) _) _
  refine RelCT.seq (RelCT.block_append (RelCT.seq
    (two_piece [.x19] s_candidated_pins (by taint_decide) head_first)
    (two_piece [.x11] s_head_pins (by taint_decide) head_second))) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.2.trans h₂.2.2.2.symm)
    (leafB SPoint.inputs (fun _ _ h => h.1.1.any) s_accept_ct) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => by rw [eval_zero, eval_zero, h₁.1.2.1, h₂.1.2.1]) ?_ ?_
  · exact s_short_ct.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, h₁.1, h₂.1, hsp⟩) fun _ _ h => h
  · exact s_rejected_ct.mono (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, h₁.1, h₂.1, hsp⟩) fun _ _ h => h

/-! ## An iteration -/

/-- Whether the search goes on after an iteration from `q`. -/
def sContinues (q : SPoint) : Prop :=
  q.k ≠ 0 ∧ (q.status = 2 ∨ q.status = 3) ∧ q.cand ≠ 0

instance (q : SPoint) : Decidable (sContinues q) := by unfold sContinues; infer_instance

theorem continues_iff {q : SPoint} {original s : State} (hl : SLive q.inputs original q.used q.k s)
    (ht : (tailOf q.inputs original q.used q.k).trace = q.trace) (hk : q.k ≠ 0) :
    Continues q.inputs original q.used q.k ↔ sContinues q := by
  unfold Continues sContinues
  rw [SCTL.status_eq ht hk, SCTL.cand_eq hl ht hk]

/-- After the test of the counted candidates, the candidate and its classification. -/
def SBranchResult (q : SPoint) (t : State) : Prop :=
  if sContinues q then SCTL (nextPoint q) t ∧ word t.mem q.inputs.F 112 = 4
  else ∃ original r, SDone q.inputs original r t

theorem branch_x19 {q : SPoint} {t : State} (h : SBranchResult q t) :
    t.gpr .x19 = q.inputs.F := by
  unfold SBranchResult at h
  split at h
  · obtain ⟨⟨_, hl, _⟩, _⟩ := h
    exact hl.x19
  · obtain ⟨_, _, hd⟩ := h
    exact hd.x19

def KGuard (q : SPoint) (s : State) : Prop :=
  SCTL q s ∧ isa.eval (.zero .x .x9) s = some (decide (q.k = 0))

theorem k_ready (q : SPoint) (s : State) (h : SCTL q s) :
    WP isa (.block [ldf .x9 0]) s (KGuard q) := by
  obtain ⟨original, h, ht⟩ := h
  exact WP.mono (k_guard h) fun _ ⟨hl, he⟩ => ⟨⟨original, hl, ht⟩, he⟩

/-- The branch of an iteration. -/
abbrev sBranch (c : Cand) : Prog isa := .ite (.zero .x .x9) exhausted (.seq (candidateRun c.call) classify)

theorem s_branch_ready (c : Cand) (q : SPoint) (s : State) (h : KGuard q s) :
    WP isa (sBranch c) s (SBranchResult q) := by
  obtain ⟨⟨original, hl, ht⟩, he⟩ := h
  refine WP.ite (decide (q.k = 0)) he ?_ ?_
  · intro hz
    have hz' := of_decide_eq_true hz
    refine WP.mono (search_exhausted hl (result := ⟨.exhausted, q.used, []⟩) rfl) fun t ht' => ?_
    have hc : ¬sContinues q := fun hc => hc.1 hz'
    unfold SBranchResult
    simp only [hc, ite_false]
    exact ⟨original, _, ht'⟩
  intro hnz
  have hk : q.k ≠ 0 := of_decide_eq_false hnz
  let final := (tailOf q.inputs original q.used q.k).consume q.used []
  refine WP.seq (WP.mono (search_candidate_run c hl) fun t ⟨htl, hp⟩ => ?_)
  refine WP.mono (search_classify (final := final) ⟨htl, [], rfl⟩ hk hp) fun r hr => ?_
  unfold SClassified at hr
  unfold SBranchResult
  by_cases hc : Continues q.inputs original q.used q.k
  · have hsc := (continues_iff hl ht hk).mp hc
    simp only [hc, ite_true] at hr
    simp only [hsc, ite_true]
    obtain ⟨⟨hrl, -⟩, h4⟩ := hr
    rw [SCTL.status_eq ht hk, SCTL.cand_eq hl ht hk] at hrl
    exact ⟨⟨original, hrl, SCTL.next_trace hl ht hk hc⟩, h4⟩
  · have hsc : ¬sContinues q := fun h => hc ((continues_iff hl ht hk).mpr h)
    simp only [hc, ite_false] at hr
    simp only [hsc, ite_false]
    exact ⟨original, _, hr⟩

theorem s_branch_ct (c : Cand) : RelCT isa (Two KGuard) (sBranch c) (fun _ _ => True) := by
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm)
    (leafB SPoint.inputs (fun _ _ h => h.1.1.any) s_exhausted_ct) ?_
  have hr : ∀ q s, KGuard q s ∧ isa.eval (.zero .x .x9) s = some false → SReady q s :=
    fun q s ⟨⟨hl, he⟩, hf⟩ => ⟨hl, of_decide_eq_false (Option.some.inj (he.symm.trans hf))⟩
  exact RelCT.seq (two_post ((s_candidate_run_ct c).mono
      (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, hr q _ h₁, hr q _ h₂, hsp⟩) fun _ _ h => h)
    fun q s h => s_candidate_ready c q s (hr q s h)) s_classify_ct

theorem s_iteration_ct (c : Cand) :
    RelCT isa (Two SCTL) (iteration c.call) (fun _ _ => True) := by
  unfold iteration
  refine RelCT.seq (two_piece [.x19] s_ctl_pins (by taint_decide) k_ready) ?_
  exact RelCT.seq (two_post (s_branch_ct c) (s_branch_ready c))
    (two_taint [.x19] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact (branch_x19 h₁).trans (branch_x19 h₂).symm) (by taint_decide))

def SCTStep (q : SPoint) (s : State) : Prop :=
  if sContinues q then isa.eval (.zero .x .x9) s = some true ∧ SCTL (nextPoint q) s
  else isa.eval (.zero .x .x9) s = some false

theorem s_ct_step (c : Cand) (q : SPoint) (s : State) (h : SCTL q s) :
    WP isa (iteration c.call) s (SCTStep q) := by
  unfold iteration
  refine WP.seq (WP.mono (k_ready q s h) fun u hu => ?_)
  refine WP.seq (WP.mono (s_branch_ready c q u hu) fun t ht => ?_)
  unfold SBranchResult at ht
  unfold SCTStep
  by_cases hc : sContinues q
  · simp only [hc, ite_true] at ht ⊢
    obtain ⟨⟨original, hl, htr⟩, hw⟩ := ht
    exact WP.mono (live_loop_guard hl hw) fun z ⟨hz, hzl⟩ => ⟨hz, original, hzl, htr⟩
  · simp only [hc, ite_false] at ht ⊢
    obtain ⟨_, _, hd⟩ := ht
    exact WP.mono (done_loop_guard hd) fun z ⟨hz, _⟩ => hz

private def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ q, n = q.inputs.randLen - q.used + 1 ∧ SCTL q s ∧ SCTL q t ∧ s.sp = t.sp

private theorem iteration_pair (c : Cand) (n : Nat) :
    RelCT isa (LoopPair n) (iteration c.call) fun s t =>
      isa.eval (.zero .x .x9) s = isa.eval (.zero .x .x9) t ∧
      (isa.eval (.zero .x .x9) s = some false → True) ∧
      (isa.eval (.zero .x .x9) s = some true → ∃ m < n, LoopPair m s t) := by
  have hw (q : SPoint) (s : State) (h : n = q.inputs.randLen - q.used + 1 ∧ SCTL q s) :
      WP isa (iteration c.call) s fun t => n = q.inputs.randLen - q.used + 1 ∧ SCTStep q t :=
    WP.mono (s_ct_step c q s h.2) fun _ ht => ⟨h.1, ht⟩
  have hc := two_post ((s_iteration_ct c).mono
    (fun _ _ ⟨q, h₁, h₂, hsp⟩ => ⟨q, h₁.2, h₂.2, hsp⟩) (fun _ _ h => h)) hw
  refine hc.mono (fun _ _ ⟨q, hn, h₁, h₂, hsp⟩ => ⟨q, ⟨hn, h₁⟩, ⟨hn, h₂⟩, hsp⟩) ?_
  rintro s t ⟨q, ⟨hn, h₁⟩, ⟨_, h₂⟩, hsp⟩
  unfold SCTStep at h₁ h₂
  by_cases hb : sContinues q
  · simp only [hb, ite_true] at h₁ h₂
    refine ⟨h₁.1.trans h₂.1.symm, fun _ => trivial, fun _ => ?_⟩
    refine ⟨(nextPoint q).inputs.randLen - (nextPoint q).used + 1, ?_, nextPoint q, rfl, h₁.2, h₂.2, hsp⟩
    obtain ⟨_, hl, _⟩ := h₁.2
    have hu := hl.used_le
    have := hb.2.2
    simp only [nextPoint] at hu ⊢
    omega
  · simp only [hb, ite_false] at h₁ h₂
    exact ⟨h₁.trans h₂.symm, fun _ => trivial, fun ht => absurd (ht.symm.trans h₁) (by decide)⟩

theorem s_loop_ct (c : Cand) :
    RelCT isa (Two SCTL) (.loop (iteration c.call) (.zero .x .x9)) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨q, hs, ht, hsp⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration c.call) (c := .zero .x .x9)
    (Q := fun _ _ => True) LoopPair (iteration_pair c) (q.inputs.randLen - q.used + 1)
    _ _ _ _ _ _ ⟨q, rfl, hs, ht, hsp⟩ he₁ he₂

end VG.Proof.RsaKeyGen.AArch64.Search
