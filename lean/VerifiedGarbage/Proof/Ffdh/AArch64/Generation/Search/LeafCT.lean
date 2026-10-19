module
public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Call

import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Writes
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Search.Writes
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # Public positions in the parameter search, its exits and its candidate (AArch64)

Two runs agree on the public descriptor (the tape included), the octets
consumed and the attempts left, which fix everything the search does from
there. The exits, the rejection and the request use only public addresses;
the candidate leaks only its public arguments and tape.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Spec.Ffdh
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.Control (writeController)
open VG.Proof.Ffdh.AArch64.ParameterCandidate (pcPre pcPub pcRand)
open VG.Impl.Ffdh.AArch64.Generation.Search

/-- Some loop state of the search with the public descriptor `p`. -/
def SAny (p : SPub) (s : State) : Prop := ∃ original used k, SLive p original used k s

structure SPoint where
  inputs : SPub
  used : Nat
  k : Nat

def SCTL (q : SPoint) (s : State) : Prop := ∃ original, SLive q.inputs original q.used q.k s

theorem SCTL.any {q : SPoint} {s : State} (h : SCTL q s) : SAny q.inputs s :=
  let ⟨original, h⟩ := h; ⟨original, _, _, h⟩

theorem s_any_pins : Pins SAny [.x19] := by
  intro p s t ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.x19.trans h₂.x19.symm

theorem s_ctl_pins : Pins SCTL [.x19] :=
  fun _ _ _ h₁ h₂ => s_any_pins _ _ _ h₁.any h₂.any

theorem no_pins {α : Type} {Φ : α → State → Prop} : Pins Φ [] := fun _ _ _ _ _ _ h => by cases h

/-! ## Zeros at `out` and the exits -/

/-- Before the zeroing's loop: its pointer and count. -/
def SZeroCT (p : SPub) (s : State) : Prop :=
  SAny p s ∧ s.gpr .x1 = p.op + BitVec.ofNat 64 0 ∧ s.gpr .x2 = BitVec.ofNat 64 p.len

private theorem zero_header (p : SPub) (s : State) (h : SAny p s) :
    WP isa (.block [ldf .x1 5, ldf .x2 6, Impl.Bignum.AArch64.movi .x3 0]) s (SZeroCT p) := by
  obtain ⟨original, used, k, h⟩ := h
  have a := h.access
  have hk : word s.mem p.control 48 = BitVec.ofNat 64 p.len :=
    h.header (j := 6) (by simp [SPub.headers])
  have hp : word s.mem p.control 40 = p.op := h.header (j := 5) (by simp [SPub.headers])
  simp only [Bignum.word, off] at hk hp
  refine WP.mono (WP.keep [.x1, .x2, .x3] (Q := fun t => (t.gpr .x1 = p.op + BitVec.ofNat 64 0 ∧
    t.gpr .x2 = BitVec.ofNat 64 p.len) ∧ t.mem = s.mem) ?_ (by decide) (by decide) (by decide +kernel))
    fun _ ⟨⟨hr, hm⟩, k⟩ => ⟨⟨original, used, _, h.keep k hm⟩, hr⟩
  brun [ldf, h.x19, hp, hk, a.ld 40 (by decide), a.ld 48 (by decide), imm64 (show 0 < 65536 by decide)]

theorem s_zero_ct : RelCT isa (Two SAny) zeroOut (fun _ _ => True) := by
  unfold zeroOut
  refine RelCT.seq (two_piece [.x19] s_any_pins (by taint_decide) zero_header) ?_
  exact two_taint [.x1, .x2] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.trans h₂.2.2.symm]) (by taint_decide)

private theorem terminal_ready (p : SPub) (s : State) (h : SAny p s) :
    WP isa (.block (terminal 3)) s (SAny p) := by
  obtain ⟨original, used, k, h⟩ := h
  exact WP.mono (terminal_live h (.inr rfl)) fun _ ⟨ht, _⟩ => ⟨original, used, 0, ht⟩

theorem s_exhausted_ct : RelCT isa (Two SAny) exhausted (fun _ _ => True) := by
  unfold exhausted
  exact RelCT.seq (two_piece [.x19] s_any_pins (by taint_decide) terminal_ready) s_zero_ct

theorem s_accept_ct : RelCT isa (Two SAny) (.block accept) (fun _ _ => True) :=
  two_taint [.x19] s_any_pins (by taint_decide)

theorem s_reject_ct : RelCT isa (Two SAny) (.block reject) (fun _ _ => True) :=
  two_taint [.x19] s_any_pins (by taint_decide)

theorem s_request_ct : RelCT isa (Two SAny) (.block request) (fun _ _ => True) :=
  two_taint [.x19] s_any_pins (by taint_decide)

/-! ## The candidate -/

/-- A loop state at which the controller runs a candidate. -/
def SReady (q : SPoint) (s : State) : Prop := SCTL q s ∧ q.k ≠ 0

/-- The candidate's entry, before the call. -/
def SCallCT (q : SPoint) (u : State) : Prop :=
  ∃ original s, SLive q.inputs original q.used q.k s ∧ q.k ≠ 0 ∧
    SArgs q.inputs q.used u ∧ u.mem = writeController s.mem (callSp q.inputs) (callValues q.inputs) ∧
    Keep argRegsW (allocated 16 s) u

def SAllocated (q : SPoint) (u : State) : Prop := ∃ s, SReady q s ∧ u = allocated 16 s

theorem s_allocated_pins : Pins SAllocated [.x19] := by
  rintro q _ _ ⟨a, ⟨⟨_, h₁⟩, _⟩, rfl⟩ ⟨b, ⟨⟨_, h₂⟩, _⟩, rfl⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.x19.trans h₂.x19.symm

private theorem arguments_ready (q : SPoint) (u : State) (h : SAllocated q u) :
    WP isa (.block arguments) u (SCallCT q) := by
  obtain ⟨s, ⟨⟨original, h⟩, hk⟩, rfl⟩ := h
  exact WP.mono (search_arguments_ok h) fun _ ⟨⟨ha, hm⟩, k⟩ => ⟨original, s, h, hk, ha, hm, k⟩

/-- What the candidate sees at its entry, in terms of the point alone. -/
private theorem call_view {q : SPoint} {u : State} (h : SCallCT q u) :
    (callState q.inputs q.used u).sp = callSp q.inputs ∧
    pcRand (callState q.inputs q.used u) = q.inputs.rand.drop q.used ∧
    SArgs q.inputs q.used (callState q.inputs q.used u) ∧
    stackArg (callState q.inputs q.used u) 0 = BitVec.ofNat 64 (q.inputs.Z / 8) := by
  obtain ⟨original, s, h, _, ha, hm, k⟩ := h
  have hu : u.sp = callSp q.inputs := by rw [k.sp]; show s.sp - BitVec.ofNat 64 16 = _; rw [h.sp]
  refine ⟨by simp only [State.withRegions_sp, State.callEntry_sp, hu], call_rand h hm ha, ?_,
    by rw [call_stackArg]; exact call_arg hu hm⟩
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := ha
  exact ⟨(call_gpr (by decide)).trans r0, (call_gpr (by decide)).trans r1, (call_gpr (by decide)).trans r2,
    (call_gpr (by decide)).trans r3, (call_gpr (by decide)).trans r4, (call_gpr (by decide)).trans r5,
    (call_gpr (by decide)).trans r6, (call_gpr (by decide)).trans r7⟩

private theorem call_pub {q : SPoint} {u₁ u₂ : State} (h₁ : SCallCT q u₁) (h₂ : SCallCT q u₂) :
    pcPub (callState q.inputs q.used u₁) (callState q.inputs q.used u₂) := by
  obtain ⟨a₁, b₁, ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩, d₁⟩ := call_view h₁
  obtain ⟨a₂, b₂, ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩, d₂⟩ := call_view h₂
  exact ⟨a₁.trans a₂.symm, by rw [b₁, b₂], c0.trans e0.symm, c1.trans e1.symm, c2.trans e2.symm,
    c3.trans e3.symm, by rw [c4, e4], c5.trans e5.symm, c6.trans e6.symm, c7.trans e7.symm,
    d₁.trans d₂.symm⟩

private theorem call_ready {q : SPoint} {u : State} (h : SCallCT q u) :
    pcPre (callState q.inputs q.used u) ∧
      Covers (callRd q.inputs q.used ++ callWr q.inputs) (u.rd ++ u.wr) ∧
      Covers (callWr q.inputs) u.wr := by
  obtain ⟨original, s, h, _, ha, hm, k⟩ := h
  have hu : u.sp = callSp q.inputs := by rw [k.sp]; show s.sp - BitVec.ofNat 64 16 = _; rw [h.sp]
  exact ⟨call_candidate_pre h.callFacts hu ha hm, call_covers_reads h k.rd k.wr,
    call_covers_writes h k.wr⟩

theorem s_candidate_call_ct (c : Cand) :
    RelCT isa (Two SCallCT) c.call (fun _ _ => True) := by
  refine RelCT.callEx c.correct c.ct fun u₁ u₂ ⟨q, h₁, h₂, _⟩ => ?_
  obtain ⟨p₁, c₁, w₁⟩ := call_ready h₁
  obtain ⟨p₂, c₂, w₂⟩ := call_ready h₂
  exact ⟨_, _, _, _, p₁, p₂, call_pub h₁ h₂, c₁, w₁, c₂, w₂⟩

theorem s_candidate_run_ct (c : Cand) :
    RelCT isa (Two SReady) (candidateRun c.call) (fun _ _ => True) := by
  unfold candidateRun
  apply RelCT.alloc
  refine (RelCT.seq (two_piece [.x19] s_allocated_pins (by taint_decide) arguments_ready)
    (s_candidate_call_ct c)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocated, hsp]⟩

/-- After the candidate. -/
def SCandidated (q : SPoint) (t : State) : Prop :=
  ∃ original, SLive q.inputs original q.used q.k t ∧ q.k ≠ 0 ∧ CandPost q.inputs q.used t

theorem s_candidate_ready (c : Cand) (q : SPoint) (s : State) (h : SReady q s) :
    WP isa (candidateRun c.call) s (SCandidated q) := by
  obtain ⟨⟨original, h⟩, hk⟩ := h
  exact WP.mono (search_candidate_run c h) fun _ ⟨ht, hp⟩ => ⟨original, ht, hk, hp⟩

end VG.Proof.Ffdh.AArch64.Generation
