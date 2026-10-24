module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.LeafCT
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Call
import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Loop
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.LeafCT
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Call
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Loop
meta import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Live
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT
meta import VerifiedGarbage.Proof.Framework.PPC64LE.Alloc
meta import VerifiedGarbage.Proof.Framework.PPC64LE.RelCT

/-! # An attempt leaks only its public arguments, the domain and its status (PPC64LE)

The attempt's timing may depend on its arguments, the domain and its status
(`gkContract.pub`). Two runs at the same point agree on all of them: the
status is the first of the statuses still to come.
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.KeyGeneration

open VG VG.PPC64LE VG.Proof.Bignum VG.Proof.Bignum.PPC64LE
open VG.PPC64LE.Taint
open VG.Proof.Ffdh.KeyGeneration
open VG.Proof.Ffdh.Control (writeController)
open VG.Proof.Ffdh.PPC64LE.GenerateKey (gkContract gkLeak gkScalar)
open VG.Impl.Ffdh.PPC64LE.KeyGeneration.Search

/-- A loop state at which the controller attempts a key. -/
def KeyReady (q : KeyPoint) (s : State) : Prop :=
  KeyCTL q s ∧ q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen

def KeyAllocated (q : KeyPoint) (u : State) : Prop := ∃ s, KeyReady q s ∧ u = allocated 128 s

/-- The attempt's entry, before the call. -/
def KeyCallCT (q : KeyPoint) (u : State) : Prop :=
  ∃ original s, KeyLive q.inputs original q.used q.keys q.scalars s ∧
    (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses ∧
    q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen ∧
    KeyArgs q.inputs q.used u ∧
    u.mem = writeController (allocated 128 s).mem (callSp q.inputs) (callValues q.inputs) ∧
    Keep argRegsW (allocated 128 s) u

/-- After the attempt. -/
def KeyAttempted (q : KeyPoint) (t : State) : Prop :=
  ∃ original, KeyLive q.inputs original q.used q.keys q.scalars t ∧
    (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses ∧
    q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen ∧
    AttemptPost q.inputs (keyRand original) q.used t

theorem key_allocated_pins : Pins KeyAllocated [.r31] := by
  rintro q _ _ ⟨a, ⟨⟨_, h₁, _⟩, _⟩, rfl⟩ ⟨b, ⟨⟨_, h₂, _⟩, _⟩, rfl⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.r31.trans h₂.r31.symm

private theorem arguments_ready (q : KeyPoint) (u : State) (h : KeyAllocated q u) :
    WP isa (.block arguments) u (KeyCallCT q) := by
  obtain ⟨s, ⟨⟨original, h, hst⟩, hk, hs, hr⟩, rfl⟩ := h
  exact WP.mono (key_arguments_ok h) fun _ ⟨⟨ha, hm⟩, k⟩ => ⟨original, s, h, hst, hk, hs, hr, ha, hm, k⟩

theorem key_attempt_ready (a : Attempt) (q : KeyPoint) (s : State) (h : KeyReady q s) :
    WP isa (attemptRun a.call) s (KeyAttempted q) := by
  obtain ⟨⟨original, h, hst⟩, hk, hs, hr⟩ := h
  exact WP.mono (key_attempt_run a h hr) fun _ ⟨ht, hp⟩ => ⟨original, ht, hst, hk, hs, hr, hp⟩

/-- The status of the attempt at a point: the first still to come. -/
def KeyPoint.status (q : KeyPoint) : Nat := q.statuses.head?.getD 0

/-- The attempt's status at a point, for each run's tape. -/
theorem attempt_status {q : KeyPoint} {original s : State}
    (h : KeyLive q.inputs original q.used q.keys q.scalars s)
    (hst : (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses)
    (hk : q.keys ≠ 0) (hs : q.scalars ≠ 0) (hr : q.used + q.inputs.len ≤ q.inputs.randLen) :
    attemptStatus q.inputs.a q.inputs.len ((keyRand original).drop q.used) = q.status := by
  have hhead := keyTail_statuses_head (a := q.inputs.a) (len := q.inputs.len)
    (rand := keyRand original) (used := q.used) hk hs (by rw [h.rand_length]; omega)
  rw [hst] at hhead
  simp only [KeyPoint.status, hhead, Option.getD_some]

/-- What the attempt sees at its entry, in terms of the point alone. -/
private theorem call_view {q : KeyPoint} {u : State} (h : KeyCallCT q u) :
    (callState q.inputs q.used u).sp = callSp q.inputs ∧
    gkLeak (callState q.inputs q.used u) = q.inputs.dom.map (·.toNat) ++ [q.status] ∧
    KeyArgs q.inputs q.used (callState q.inputs q.used u) ∧
    stackArg (callState q.inputs q.used u) 0 = BitVec.ofNat 64 q.inputs.len ∧
    stackArg (callState q.inputs q.used u) 1 = q.inputs.B ∧
    stackArg (callState q.inputs q.used u) 2 = BitVec.ofNat 64 (q.inputs.Z / 8) := by
  obtain ⟨original, s, h, hst, hk, hs, hr, ha, hm, k⟩ := h
  have hu : u.sp = callSp q.inputs := by
    rw [k.sp]; show s.sp - BitVec.ofNat 64 128 = _; rw [h.sp]
  have hf := h.callFacts hr
  obtain ⟨hdom, hrand, h9⟩ := call_inputs h hr hf hm hu ha
  have he := attempt_status h hst hk hs hr
  obtain ⟨h0, h1, h2⟩ := call_args hu hm
  refine ⟨by simp only [State.withRegions_sp, State.callEntry_sp, hu], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [gkLeak, gkScalar, hdom, hrand, h9]
    rw [← he]
    rfl
  · obtain ⟨r3, r4, r5, r6, r7, r8, r9, r10⟩ := ha
    exact ⟨(call_gpr (by decide)).trans r3, (call_gpr (by decide)).trans r4, (call_gpr (by decide)).trans r5,
      (call_gpr (by decide)).trans r6, (call_gpr (by decide)).trans r7, (call_gpr (by decide)).trans r8,
      (call_gpr (by decide)).trans r9, (call_gpr (by decide)).trans r10⟩
  · rw [call_stackArg, h0]
  · rw [call_stackArg, h1]
  · rw [call_stackArg, h2]

private theorem call_pub {q : KeyPoint} {u₁ u₂ : State} (h₁ : KeyCallCT q u₁) (h₂ : KeyCallCT q u₂) :
    gkContract.pub (callState q.inputs q.used u₁) (callState q.inputs q.used u₂) := by
  obtain ⟨a₁, b₁, ⟨c3, c4, c5, c6, c7, c8, c9, c10⟩, d₀, d₁, d₂⟩ := call_view h₁
  obtain ⟨a₂, b₂, ⟨e3, e4, e5, e6, e7, e8, e9, e10⟩, f₀, f₁, f₂⟩ := call_view h₂
  exact ⟨a₁.trans a₂.symm, c3.trans e3.symm, c4.trans e4.symm, c5.trans e5.symm, c6.trans e6.symm,
    c7.trans e7.symm, c8.trans e8.symm, c9.trans e9.symm, c10.trans e10.symm, d₀.trans f₀.symm,
    d₁.trans f₁.symm, d₂.trans f₂.symm, b₁.trans b₂.symm⟩

private theorem call_ready {q : KeyPoint} {u : State} (h : KeyCallCT q u) :
    gkContract.pre (callState q.inputs q.used u) ∧
      Covers (callRd q.inputs q.used ++ callWr q.inputs) (u.rd ++ u.wr) ∧
      Covers (callWr q.inputs) u.wr := by
  obtain ⟨original, s, h, _, _, _, hr, ha, hm, k⟩ := h
  have hu : u.sp = callSp q.inputs := by
    rw [k.sp]; show s.sp - BitVec.ofNat 64 128 = _; rw [h.sp]
  exact ⟨call_attempt_pre (h.callFacts hr) hu ha hm, call_covers_reads h hr k.rd k.wr,
    call_covers_writes h k.wr⟩

theorem key_attempt_call_ct (a : Attempt) :
    RelCT isa (Two KeyCallCT) a.call (fun _ _ => True) := by
  refine RelCT.callEx a.correct a.ct fun u₁ u₂ ⟨q, h₁, h₂, _⟩ => ?_
  obtain ⟨p₁, c₁, w₁⟩ := call_ready h₁
  obtain ⟨p₂, c₂, w₂⟩ := call_ready h₂
  exact ⟨_, _, _, _, p₁, p₂, call_pub h₁ h₂, c₁, w₁, c₂, w₂⟩

theorem key_attempt_run_ct (a : Attempt) :
    RelCT isa (Two KeyReady) (attemptRun a.call) (fun _ _ => True) := by
  unfold attemptRun
  apply RelCT.alloc
  · rintro _ _ ⟨_, _, _, hsp⟩; exact hsp
  refine (RelCT.seq (two_post (two_taint [.r31] key_allocated_pins (by taint_decide)) arguments_ready)
    (key_attempt_call_ct a)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocated, hsp]⟩

end VG.Proof.Ffdh.PPC64LE.KeyGeneration
