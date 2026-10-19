module

public import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.LeafCT
public import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.AttemptRun
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.CTTail
import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.Loop
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.LeafCT
meta import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.AttemptRun
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.CTTail
meta import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.Loop
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch

/-! # An attempt leaks only the domain and its status (AArch64)

The attempt's timing may depend on the domain and its status (`gkPub`).
Two runs at the same point agree on both: the status is the first of the
statuses still to come.
-/

@[expose] public section

namespace VG.Proof.Ffdh.AArch64.KeyGeneration

open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Ffdh.KeyGeneration
open VG.Proof.Ffdh.Control (writeController)
open VG.Proof.Ffdh.AArch64.GenerateKey (gkPub gkLeak gkDom gkRand gkA gkS gkContract gk_correct
  gk_constantTime stackArgs_three)
open VG.Impl.Ffdh.AArch64.KeyGeneration.Search

/-- A loop state at which the controller attempts a key. -/
def KeyReady (q : KeyPoint) (s : State) : Prop :=
  KeyCTL q s ∧ q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen

def KeyAllocated (q : KeyPoint) (u : State) : Prop := ∃ s, KeyReady q s ∧ u = allocated 32 s

/-- The attempt's entry, before the call. -/
def KeyCallCT (q : KeyPoint) (u : State) : Prop :=
  ∃ original s, KeyLive q.inputs original q.used q.keys q.scalars s ∧
    (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses ∧
    q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen ∧
    KeyArgs q.inputs q.used u ∧ u.mem = writeController s.mem (callSp q.inputs) (callValues q.inputs) ∧
    Keep argRegsW (allocated 32 s) u

/-- After the attempt. -/
def KeyAttempted (q : KeyPoint) (t : State) : Prop :=
  ∃ original, KeyLive q.inputs original q.used q.keys q.scalars t ∧
    (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses ∧
    q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen ∧
    AttemptPost q.inputs (keyRand original) q.used t

theorem key_allocated_pins : Pins KeyAllocated [.x19] := by
  rintro q _ _ ⟨a, ⟨⟨_, h₁, _⟩, _⟩, rfl⟩ ⟨b, ⟨⟨_, h₂, _⟩, _⟩, rfl⟩ r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact h₁.x19.trans h₂.x19.symm

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
    (∀ r ∈ argRegs, (callState q.inputs q.used u).gpr r = (match r with
      | .x0 => q.inputs.xp | .x1 => BitVec.ofNat 64 q.inputs.len | .x2 => q.inputs.yp
      | .x3 => BitVec.ofNat 64 q.inputs.len | .x4 => q.inputs.dp | .x5 => BitVec.ofNat 64 q.inputs.dlen
      | .x6 => BitVec.ofNat 64 q.inputs.len | _ => q.inputs.rp + BitVec.ofNat 64 q.used)) ∧
    List.map (stackArg (callState q.inputs q.used u)) (List.range 3) =
      [BitVec.ofNat 64 q.inputs.len, q.inputs.B, BitVec.ofNat 64 (q.inputs.Z / 8)] := by
  obtain ⟨original, s, h, hst, hk, hs, hr, ha, hm, k⟩ := h
  have hu : u.sp = callSp q.inputs := by rw [k.sp]; show s.sp - BitVec.ofNat 64 32 = _; rw [h.sp]
  have hf := h.callFacts hr
  obtain ⟨hdom, hrand, h6⟩ := call_inputs h hr hf hm hu ha
  have he := attempt_status h hst hk hs hr
  obtain ⟨h0, h1, h2⟩ := call_args hu hm
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := ha
  refine ⟨by simp only [State.withRegions_sp, State.callEntry_sp, hu], ?_, ?_, ?_⟩
  · simp only [gkLeak, gkA, gkS, hdom, hrand, h6]
    rw [← he]
    rfl
  · intro r hr'
    simp only [argRegs, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [call_gpr (by decide)] <;> with_reducible assumption
  · rw [stackArgs_three, call_stackArg, call_stackArg, call_stackArg, h0, h1, h2]

private theorem call_pub {q : KeyPoint} {u₁ u₂ : State} (h₁ : KeyCallCT q u₁) (h₂ : KeyCallCT q u₂) :
    gkPub (callState q.inputs q.used u₁) (callState q.inputs q.used u₂) := by
  obtain ⟨a₁, b₁, c₁, d₁⟩ := call_view h₁
  obtain ⟨a₂, b₂, c₂, d₂⟩ := call_view h₂
  exact ⟨fun r hr => (c₁ r hr).trans (c₂ r hr).symm, a₁.trans a₂.symm, d₁.trans d₂.symm,
    b₁.trans b₂.symm⟩

private theorem call_ready {q : KeyPoint} {u : State} (h : KeyCallCT q u) :
    gkContract.pre (callState q.inputs q.used u) ∧
      Covers (callRd q.inputs q.used ++ callWr q.inputs) (u.rd ++ u.wr) ∧
      Covers (callWr q.inputs) u.wr := by
  obtain ⟨original, s, h, _, _, _, hr, ha, hm, k⟩ := h
  have hu : u.sp = callSp q.inputs := by rw [k.sp]; show s.sp - BitVec.ofNat 64 32 = _; rw [h.sp]
  exact ⟨call_attempt_pre (h.callFacts hr) hu ha hm, call_covers_reads h hr k.rd k.wr,
    call_covers_writes h k.wr⟩

theorem key_attempt_call_ct (a : Attempt) :
    RelCT isa (Two KeyCallCT) a.call (fun _ _ => True) := by
  refine RelCT.callEx (gk_correct a.W a.M a.S) (gk_constantTime a.W a.M a.S) fun u₁ u₂ ⟨q, h₁, h₂, _⟩ => ?_
  obtain ⟨p₁, c₁, w₁⟩ := call_ready h₁
  obtain ⟨p₂, c₂, w₂⟩ := call_ready h₂
  exact ⟨_, _, _, _, p₁, p₂, call_pub h₁ h₂, c₁, w₁, c₂, w₂⟩

theorem key_attempt_run_ct (a : Attempt) :
    RelCT isa (Two KeyReady) (attemptRun a.call) (fun _ _ => True) := by
  unfold attemptRun
  apply RelCT.alloc
  refine (RelCT.seq (two_piece [.x19] key_allocated_pins (by taint_decide) arguments_ready)
    (key_attempt_call_ct a)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂, hsp⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩, by simp only [allocated, hsp]⟩

end VG.Proof.Ffdh.AArch64.KeyGeneration
