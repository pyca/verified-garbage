module

public import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Classify
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.Search.Classify
meta import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
meta import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! # The RSA prime search's timing: the exits and the candidate (AArch64)

Two runs from the same public descriptor are at the same point of the
search: the same octets consumed, counted candidates left and trace of the
search from there. The trace gives the next candidate's leak
(`SCTL.leak`), so its status and consumption: both runs then take the same
branches.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.AArch64.Search

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.Control (writeController)
open VG.Proof.Ffdh.AArch64.Generation (imm64)
open VG.Proof.RsaKeyGen.AArch64 (candPre candPub candLeak)
open VG.Impl.RsaKeyGen.AArch64.Search

/-- Some loop state of the search with the public descriptor `p`. -/
def SAny (p : SPub) (s : State) : Prop := ∃ original used k, SLive p original used k s

structure SPoint where
  inputs : SPub
  used : Nat
  k : Nat
  trace : List Nat

def SCTL (q : SPoint) (s : State) : Prop :=
  ∃ original, SLive q.inputs original q.used q.k s ∧ (tailOf q.inputs original q.used q.k).trace = q.trace

theorem SCTL.any {q : SPoint} {s : State} (h : SCTL q s) : SAny q.inputs s :=
  let ⟨original, h, _⟩ := h; ⟨original, _, _, h⟩

theorem s_any_pins : Pins SAny [.x19] := by
  intro p s t ⟨_, _, _, h₁⟩ ⟨_, _, _, h₂⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.x19.trans h₂.x19.symm

theorem s_ctl_pins : Pins SCTL [.x19] :=
  fun _ _ _ h₁ h₂ => s_any_pins _ _ _ h₁.any h₂.any

theorem no_pins {α : Type} {Φ : α → State → Prop} : Pins Φ [] := fun _ _ _ _ _ _ h => by cases h

/-! ## What the trace says -/

/-- The next candidate's leak, from the trace. -/
def SPoint.leak (q : SPoint) : List Nat := (q.trace.drop 1).take (q.trace.headD 0)

/-- The next candidate's status, from the point. -/
abbrev SPoint.status (q : SPoint) : Nat := VG.Proof.RsaKeyGen.Search.statusOfLeak q.leak

/-- The octets the next candidate consumes, from the point. -/
abbrev SPoint.cand (q : SPoint) : Nat := VG.Proof.RsaKeyGen.Search.usedOfLeak q.inputs.len q.leak

/-- The point past a rejected candidate. -/
def nextPoint (q : SPoint) : SPoint :=
  ⟨q.inputs, q.used + q.cand, nextK q.status q.k, q.trace.drop (q.trace.headD 0 + 1)⟩

theorem SCTL.leak_eq {q : SPoint} {original : State}
    (ht : (tailOf q.inputs original q.used q.k).trace = q.trace) (hk : q.k ≠ 0) :
    Spec.RsaKeyGen.candidateLeak q.inputs.len q.inputs.eB (searchP original)
      ((searchRand original).drop q.used) = q.leak := by
  obtain ⟨rest, hrest⟩ := VG.Proof.RsaKeyGen.Search.search_trace (L := q.inputs.len) (eB := q.inputs.eB)
    (pB := searchP original) hk ((searchRand original).drop q.used)
  unfold tailOf SPub.tail at ht
  rw [hrest] at ht
  unfold SPoint.leak
  rw [← ht]
  simp [VG.Proof.RsaKeyGen.Search.entry]

theorem SCTL.status_eq {q : SPoint} {original : State}
    (ht : (tailOf q.inputs original q.used q.k).trace = q.trace) (hk : q.k ≠ 0) :
    candStatus q.inputs original q.used = q.status := by
  rw [candStatus, VG.Proof.RsaKeyGen.Search.status_of_leak, SCTL.leak_eq ht hk]

theorem SCTL.cand_eq {q : SPoint} {original s : State} (hl : SLive q.inputs original q.used q.k s)
    (ht : (tailOf q.inputs original q.used q.k).trace = q.trace) (hk : q.k ≠ 0) :
    candUsed q.inputs original q.used = q.cand := by
  have hu := VG.Proof.RsaKeyGen.Search.used_of_leak (L := q.inputs.len) (eB := q.inputs.eB)
    (pB := searchP original) ((searchRand original).drop q.used)
  rw [SCTL.leak_eq ht hk, List.length_drop, hl.rand_length] at hu
  unfold candUsed cand
  exact hu

/-- Past a rejected candidate, the trace of the search from there. -/
theorem SCTL.next_trace {q : SPoint} {original s : State} (hl : SLive q.inputs original q.used q.k s)
    (ht : (tailOf q.inputs original q.used q.k).trace = q.trace) (hk : q.k ≠ 0)
    (hc : Continues q.inputs original q.used q.k) :
    (tailOf q.inputs original (q.used + q.cand) (nextK q.status q.k)).trace =
      q.trace.drop (q.trace.headD 0 + 1) := by
  obtain ⟨-, hst, hu0⟩ := hc
  have hl' := hl.rand_length
  rcases hcand : cand q.inputs original q.used with _ | ⟨x, rest⟩
  · simp [candStatus, hcand, Spec.RsaKeyGen.candidateStatus] at hst
  · have hx : x = .close ∨ x = .rejected := by
      cases x <;> simp_all [candStatus, Spec.RsaKeyGen.candidateStatus]
    have hpast := tail_past hk hl' hcand hx hu0
    rw [SCTL.status_eq ht hk, SCTL.cand_eq hl ht hk] at hpast
    rw [hpast] at ht
    simp only [Spec.Entropy.Result.consume] at ht
    rw [← ht]
    simp only [VG.Proof.RsaKeyGen.Search.entry, List.cons_append, List.headD_cons, List.drop_succ_cons,
      List.drop_left]

/-! ## Zeros at `out` and the exits -/

/-- Before the zeroing's loop: its pointer and count. -/
def SZeroCT (p : SPub) (s : State) : Prop :=
  SAny p s ∧ s.gpr .x1 = p.op + BitVec.ofNat 64 0 ∧ s.gpr .x2 = BitVec.ofNat 64 p.len

private theorem zero_header (p : SPub) (s : State) (h : SAny p s) :
    WP isa (.block [ldf .x1 5, ldf .x2 6, Impl.Bignum.AArch64.movi .x3 0]) s (SZeroCT p) := by
  obtain ⟨original, used, k, h⟩ := h
  have a := h.access
  have hk : word s.mem p.F 48 = BitVec.ofNat 64 p.len := h.header (j := 6) (by simp [SPub.headers])
  have hp : word s.mem p.F 40 = p.op := h.header (j := 5) (by simp [SPub.headers])
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

/-- A loop state at which the search runs a candidate. -/
def SReady (q : SPoint) (s : State) : Prop := SCTL q s ∧ q.k ≠ 0

/-- The candidate's entry, before the call. -/
def SCallCT (q : SPoint) (u : State) : Prop :=
  ∃ original s, SLive q.inputs original q.used q.k s ∧
    (tailOf q.inputs original q.used q.k).trace = q.trace ∧ q.k ≠ 0 ∧
    SArgs q.inputs q.used u ∧ u.mem = writeController s.mem (callSp q.inputs) (callValues q.inputs q.used) ∧
    Keep argRegsW (allocated 32 s) u

def SAllocated (q : SPoint) (u : State) : Prop := ∃ s, SReady q s ∧ u = allocated 32 s

theorem s_allocated_pins : Pins SAllocated [.x19] := by
  rintro q _ _ ⟨a, ⟨⟨_, h₁, _⟩, _⟩, rfl⟩ ⟨b, ⟨⟨_, h₂, _⟩, _⟩, rfl⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.x19.trans h₂.x19.symm

private theorem arguments_ready (q : SPoint) (u : State) (h : SAllocated q u) :
    WP isa (.block arguments) u (SCallCT q) := by
  obtain ⟨s, ⟨⟨original, h, ht⟩, hk⟩, rfl⟩ := h
  exact WP.mono (search_arguments_ok h) fun _ ⟨⟨ha, hm⟩, k⟩ => ⟨original, s, h, ht, hk, ha, hm, k⟩

/-- What the candidate sees at its entry, in terms of the point alone. -/
private theorem call_view {q : SPoint} {u : State} (h : SCallCT q u) :
    (callState q.inputs q.used u).sp = callSp q.inputs ∧
    SArgs q.inputs q.used (callState q.inputs q.used u) ∧
    stackArg (callState q.inputs q.used u) 0 = BitVec.ofNat 64 (q.inputs.randLen - q.used) ∧
    stackArg (callState q.inputs q.used u) 1 = q.inputs.B ∧
    stackArg (callState q.inputs q.used u) 2 = BitVec.ofNat 64 (q.inputs.Z / 8) ∧
    candLeak (callState q.inputs q.used u) = q.inputs.eB.map (·.toNat) ++ q.leak := by
  obtain ⟨original, s, h, ht, hk, ha, hm, k⟩ := h
  have hf := h.callFacts
  have hu : u.sp = callSp q.inputs := by rw [k.sp]; show s.sp - BitVec.ofNat 64 32 = _; rw [h.sp]
  obtain ⟨a0, a1, a2⟩ := call_args hu hm
  obtain ⟨he, hpb, hrand⟩ := call_inputs h hm ha
  have hrl : (BitVec.ofNat 64 (q.inputs.randLen - q.used)).toNat = q.inputs.randLen - q.used :=
    toNat_ofNat_lt (by have := hf.randLen; omega_arith)
  have hlen : (BitVec.ofNat 64 q.inputs.len).toNat = q.inputs.len := toNat_ofNat_lt hf.len_lt
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := ha
  refine ⟨by simp only [State.withRegions_sp, State.callEntry_sp, hu],
    ⟨(call_gpr (by decide)).trans r0, (call_gpr (by decide)).trans r1, (call_gpr (by decide)).trans r2,
    (call_gpr (by decide)).trans r3, (call_gpr (by decide)).trans r4, (call_gpr (by decide)).trans r5,
    (call_gpr (by decide)).trans r6, (call_gpr (by decide)).trans r7⟩,
    by rw [call_stackArg]; exact a0, by rw [call_stackArg]; exact a1, by rw [call_stackArg]; exact a2, ?_⟩
  unfold candLeak
  rw [call_stackArg, a0, hrl, he, hpb, hrand,
    call_gpr (by decide : Reg.x1 ∉ linkRegs), r1, hlen, SCTL.leak_eq ht hk]

private theorem call_pub {q : SPoint} {u₁ u₂ : State} (h₁ : SCallCT q u₁) (h₂ : SCallCT q u₂) :
    candPub (callState q.inputs q.used u₁) (callState q.inputs q.used u₂) := by
  obtain ⟨a₁, ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩, s0, s1, s2, l₁⟩ := call_view h₁
  obtain ⟨a₂, ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩, t0, t1, t2, l₂⟩ := call_view h₂
  refine ⟨fun r hr => ?_, a₁.trans a₂.symm, fun i hi => ?_, l₁.trans l₂.symm⟩
  · simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [c0.trans e0.symm, c1.trans e1.symm, c2.trans e2.symm, c3.trans e3.symm, c4.trans e4.symm,
      c5.trans e5.symm, c6.trans e6.symm, c7.trans e7.symm]
  · match i, hi with
    | 0, _ => exact s0.trans t0.symm
    | 1, _ => exact s1.trans t1.symm
    | 2, _ => exact s2.trans t2.symm

private theorem call_ready {q : SPoint} {u : State} (h : SCallCT q u) :
    candPre (callState q.inputs q.used u) ∧
      Covers (callRd q.inputs q.used ++ callWr q.inputs) (u.rd ++ u.wr) ∧
      Covers (callWr q.inputs) u.wr := by
  obtain ⟨original, s, h, _, _, ha, hm, k⟩ := h
  have hu : u.sp = callSp q.inputs := by rw [k.sp]; show s.sp - BitVec.ofNat 64 32 = _; rw [h.sp]
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
  ∃ original, SLive q.inputs original q.used q.k t ∧
    (tailOf q.inputs original q.used q.k).trace = q.trace ∧ q.k ≠ 0 ∧
    CandPost q.inputs (searchP original) (searchRand original) q.used t

theorem s_candidate_ready (c : Cand) (q : SPoint) (s : State) (h : SReady q s) :
    WP isa (candidateRun c.call) s (SCandidated q) := by
  obtain ⟨⟨original, h, ht⟩, hk⟩ := h
  exact WP.mono (search_candidate_run c h) fun _ ⟨hl, hp⟩ => ⟨original, hl, ht, hk, hp⟩

end VG.Proof.RsaKeyGen.AArch64.Search
