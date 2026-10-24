module
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Call

public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
public import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Writes
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Call
meta import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Search.Writes
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
meta import VerifiedGarbage.Proof.Framework.Offset

/-! # Public positions in the parameter search, its exits and its candidate (PPC64LE)

Two runs agree on the public descriptor (the tape included), the octets
consumed and the attempts left, which fix everything the search does from
there. The exits, the rejection and the request use only public addresses;
the candidate leaks only its public arguments and tape.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Generation

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE VG.Spec.Ffdh
open VG.PPC64LE.Taint
open VG.Proof.Ffdh.Control (writeController)
open VG.Proof.Ffdh.PPC64LE.ParameterCandidate (pcPre pcPub pcRand)
open VG.Impl.Ffdh.PPC64LE.Generation.Search

/-- Some loop state of the search with the public descriptor `p`. -/
def SAny (p : SPub) (s : State) : Prop := ∃ original used k, SLive p original used k s

structure SPoint where
  inputs : SPub
  used : Nat
  k : Nat

def SCTL (q : SPoint) (s : State) : Prop := ∃ original, SLive q.inputs original q.used q.k s

theorem SCTL.any {q : SPoint} {s : State} (h : SCTL q s) : SAny q.inputs s :=
  let ⟨original, h⟩ := h; ⟨original, _, _, h⟩

theorem s_any_pins : Pins SAny [.r31] := by
  intro p s t ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.r31.trans h₂.r31.symm

theorem s_ctl_pins : Pins SCTL [.r31] :=
  fun _ _ _ h₁ h₂ => s_any_pins _ _ _ h₁.any h₂.any

theorem no_pins {α : Type} {Φ : α → State → Prop} : Pins Φ [] := fun _ _ _ _ _ _ h => by cases h

/-! ## Zeros at `out` and the exits -/

/-- Before the zeroing's loop: its pointer and count. -/
def SZeroCT (p : SPub) (s : State) : Prop :=
  SAny p s ∧ s.gpr .r3 = p.op ∧ s.gpr .r4 = BitVec.ofNat 64 p.len

private theorem zero_header (p : SPub) (s : State) (h : SAny p s) :
    WP isa (.block [ldf .r3 5, ldf .r4 6, .li .r5 0]) s (SZeroCT p) := by
  obtain ⟨original, used, k, h⟩ := h
  have a := h.access
  have hk : word s.mem p.control 48 = BitVec.ofNat 64 p.len :=
    h.header (j := 6) (by simp [SPub.headers])
  have hp : word s.mem p.control 40 = p.op := h.header (j := 5) (by simp [SPub.headers])
  simp only [Bignum.word, off] at hk hp
  refine WP.mono (WP.keep [.r3, .r4, .r5] (Q := fun t => (t.gpr .r3 = p.op ∧
    t.gpr .r4 = BitVec.ofNat 64 p.len) ∧ t.mem = s.mem) ?_ (by decide))
    fun _ ⟨⟨hr, hm⟩, k⟩ => ⟨⟨original, used, _, h.keep k hm⟩, hr⟩
  prun [ldf, h.r31, hp, hk, a.ld 40 (by decide), a.ld 48 (by decide)]

theorem s_zero_ct : RelCT isa (Two SAny) zeroOut (fun _ _ => True) := by
  unfold zeroOut
  refine RelCT.seq (two_post (two_taint [.r31] s_any_pins (by taint_decide)) zero_header) ?_
  exact two_taint [.r3, .r4] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h₁.2.1.trans h₂.2.1.symm, h₁.2.2.trans h₂.2.2.symm]) (by taint_decide)

private theorem terminal_ready (p : SPub) (s : State) (h : SAny p s) :
    WP isa (.block (terminal 3)) s (SAny p) := by
  obtain ⟨original, used, k, h⟩ := h
  exact WP.mono (terminal_live h (.inr rfl)) fun _ ⟨ht, _⟩ => ⟨original, used, 0, ht⟩

theorem s_exhausted_ct : RelCT isa (Two SAny) exhausted (fun _ _ => True) := by
  unfold exhausted
  exact RelCT.seq (two_post (two_taint [.r31] s_any_pins (by taint_decide)) terminal_ready) s_zero_ct

theorem s_accept_ct : RelCT isa (Two SAny) (.block accept) (fun _ _ => True) :=
  two_taint [.r31] s_any_pins (by taint_decide)

theorem s_reject_ct : RelCT isa (Two SAny) (.block reject) (fun _ _ => True) :=
  two_taint [.r31] s_any_pins (by taint_decide)

theorem s_request_ct : RelCT isa (Two SAny) (.block request) (fun _ _ => True) :=
  two_taint [.r31] s_any_pins (by taint_decide)

/-! ## The candidate -/

/-- A loop state at which the controller runs a candidate. -/
def SReady (q : SPoint) (s : State) : Prop := SCTL q s ∧ q.k ≠ 0

/-- The candidate's entry, before the call. -/
def SCallCT (q : SPoint) (u : State) : Prop :=
  ∃ original s, SLive q.inputs original q.used q.k s ∧ q.k ≠ 0 ∧
    SArgs q.inputs q.used u ∧
    u.mem = writeController (allocated 112 s).mem (callSp q.inputs) (callValues q.inputs) ∧
    Keep argRegsW (allocated 112 s) u

def SAllocated (q : SPoint) (u : State) : Prop := ∃ s, SReady q s ∧ u = allocated 112 s

theorem s_allocated_pins : Pins SAllocated [.r31] := by
  rintro q _ _ ⟨a, ⟨⟨_, h₁⟩, _⟩, rfl⟩ ⟨b, ⟨⟨_, h₂⟩, _⟩, rfl⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.r31.trans h₂.r31.symm

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
  have hu : u.sp = callSp q.inputs := by
    rw [k.sp]; show s.sp - BitVec.ofNat 64 112 = _; rw [h.sp]; exact callSp_eq _
  refine ⟨by simp only [State.withRegions_sp, State.callEntry_sp, hu], call_rand h hm ha, ?_,
    call_arg hu hm⟩
  obtain ⟨r3, r4, r5, r6, r7, r8, r9, r10⟩ := ha
  exact ⟨(call_gpr (by decide)).trans r3, (call_gpr (by decide)).trans r4, (call_gpr (by decide)).trans r5,
    (call_gpr (by decide)).trans r6, (call_gpr (by decide)).trans r7, (call_gpr (by decide)).trans r8,
    (call_gpr (by decide)).trans r9, (call_gpr (by decide)).trans r10⟩

private theorem call_pub {q : SPoint} {u₁ u₂ : State} (h₁ : SCallCT q u₁) (h₂ : SCallCT q u₂) :
    pcPub (callState q.inputs q.used u₁) (callState q.inputs q.used u₂) := by
  obtain ⟨a₁, b₁, ⟨c3, c4, c5, c6, c7, c8, c9, c10⟩, d₁⟩ := call_view h₁
  obtain ⟨a₂, b₂, ⟨e3, e4, e5, e6, e7, e8, e9, e10⟩, d₂⟩ := call_view h₂
  exact ⟨a₁.trans a₂.symm, by rw [b₁, b₂], c3.trans e3.symm, c4.trans e4.symm, c5.trans e5.symm,
    c6.trans e6.symm, by rw [c7, e7], c8.trans e8.symm, c9.trans e9.symm, c10.trans e10.symm,
    d₁.trans d₂.symm⟩

private theorem call_ready {q : SPoint} {u : State} (h : SCallCT q u) :
    pcPre (callState q.inputs q.used u) ∧
      Covers (callRd q.inputs q.used ++ callWr q.inputs) (u.rd ++ u.wr) ∧
      Covers (callWr q.inputs) u.wr := by
  obtain ⟨original, s, h, _, ha, hm, k⟩ := h
  have hu : u.sp = callSp q.inputs := by
    rw [k.sp]; show s.sp - BitVec.ofNat 64 112 = _; rw [h.sp]; exact callSp_eq _
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
  · rintro _ _ ⟨_, _, _, hsp⟩; exact hsp
  refine (RelCT.seq (two_post (two_taint [.r31] s_allocated_pins (by taint_decide)) arguments_ready)
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

end VG.Proof.Ffdh.PPC64LE.Generation
