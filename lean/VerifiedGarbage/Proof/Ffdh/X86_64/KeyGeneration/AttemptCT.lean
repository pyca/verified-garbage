module

public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.CTData
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Attempt
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.AttemptRun
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.AttemptStep
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.CallEntry
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.CTData
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Attempt
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.AttemptRun
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.AttemptStep
meta import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.CallEntry
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! # An attempt leaks only the domain and its status

The attempt's timing may depend on the domain and its status
(`attemptContract.pub`). Two runs at the same point agree on both: the
status is the first of the statuses still to come.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Proof.Ffdh.KeyGeneration
open VG.Proof.Ffdh.X86_64.Generation (writeController allocated allocated_rsp frame_alloc_ct)
open VG.Proof.Ffdh.X86_64.GenerateKey (gkLeak gkDom gkRand gkA gkS)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

/-- A loop state at which the controller attempts a key. -/
def KeyReady (q : KeyPoint) (s : State) : Prop :=
  KeyCTL q s ∧ q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen

def KeyAllocated (q : KeyPoint) (u : State) : Prop := ∃ s, KeyReady q s ∧ u = allocated 40 s

/-- The attempt's entry, before the call. -/
def KeyCallCT (q : KeyPoint) (u : State) : Prop :=
  ∃ original s, KeyLive q.inputs original q.used q.keys q.scalars s ∧
    (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses ∧
    q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen ∧
    KeyArgs q.inputs u ∧
    u.mem = writeController s.mem (s.gpr .rsp - 40) (callValues q.inputs q.used) ∧
    Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11] (allocated 40 s) u

/-- After the attempt. -/
def KeyAttempted (q : KeyPoint) (t : State) : Prop :=
  ∃ original, KeyLive q.inputs original q.used q.keys q.scalars t ∧
    (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses ∧
    q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen ∧
    AttemptPost q.inputs (keyRand original) q.used t

theorem key_allocated_pins : Pins KeyAllocated [.r12, .rsp] := by
  rintro q _ _ ⟨a, ⟨⟨_, h₁, _⟩, _⟩, rfl⟩ ⟨b, ⟨⟨_, h₂, _⟩, _⟩, rfl⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h₁.r12.trans h₂.r12.symm
  · rw [allocated_rsp, allocated_rsp, h₁.rsp, h₂.rsp]

private theorem arguments_ready (q : KeyPoint) (u : State) (h : KeyAllocated q u) :
    WP isa (.block arguments) u (KeyCallCT q) := by
  obtain ⟨s, ⟨⟨original, h, hst⟩, hk, hs, hr⟩, rfl⟩ := h
  exact WP.mono (key_arguments_ok h) fun _ ⟨ha, hm, k⟩ => ⟨original, s, h, hst, hk, hs, hr, ha, hm, k⟩

theorem key_attempt_ready (v : RoundImpl) (q : KeyPoint) (s : State) (h : KeyReady q s) :
    WP isa (attemptRun (attemptCall v)) s (KeyAttempted q) := by
  obtain ⟨⟨original, h, hst⟩, hk, hs, hr⟩ := h
  exact WP.mono (key_attempt_run v h hr) fun _ ⟨ht, hp⟩ => ⟨original, ht, hst, hk, hs, hr, hp⟩

/-- What the attempt sees at its entry, in terms of the point alone. -/
private theorem call_view {q : KeyPoint} {u : State} (h : KeyCallCT q u) :
    (callState q.inputs q.used u).gpr .rsp = q.inputs.sp - 40 - 8 ∧
    gkLeak (callState q.inputs q.used u) = q.inputs.dom.map (·.toNat) ++ q.statuses.head?.toList ∧
    (callState q.inputs q.used u).gpr .rdi = q.inputs.xp ∧
    (callState q.inputs q.used u).gpr .rsi = BitVec.ofNat 64 q.inputs.len ∧
    (callState q.inputs q.used u).gpr .rdx = q.inputs.yp ∧
    (callState q.inputs q.used u).gpr .rcx = BitVec.ofNat 64 q.inputs.len ∧
    (callState q.inputs q.used u).gpr .r8 = q.inputs.dp ∧
    (callState q.inputs q.used u).gpr .r9 = BitVec.ofNat 64 q.inputs.dlen ∧
    stackArg (callState q.inputs q.used u) 0 = BitVec.ofNat 64 q.inputs.len ∧
    stackArg (callState q.inputs q.used u) 1 = q.inputs.rp + BitVec.ofNat 64 q.used ∧
    stackArg (callState q.inputs q.used u) 2 = BitVec.ofNat 64 q.inputs.len ∧
    stackArg (callState q.inputs q.used u) 3 = q.inputs.B ∧
    stackArg (callState q.inputs q.used u) 4 = BitVec.ofNat 64 (q.inputs.Z / 8) := by
  obtain ⟨original, s, h, hst, hk, hs, hr, ha, hm, k⟩ := h
  have hu : u.gpr .rsp = q.inputs.sp - 40 := by
    rw [k.gpr (by decide), allocated_rsp, h.rsp]; rfl
  have hf := h.callFacts hr
  obtain ⟨hdom, hrand, hlen⟩ := call_inputs h hr hf hm hu ha
  have hlen' : (keyRand original).length = q.inputs.randLen := by
    rw [← h.random]; simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  have hhead := keyTail_statuses_head (a := q.inputs.a) (len := q.inputs.len) (rand := keyRand original) (used := q.used)
    hk hs (by rw [hlen']; omega)
  rw [hst] at hhead
  obtain ⟨h0, h1, h2, h3, h4⟩ := call_args hu h.rsp hm
  obtain ⟨hdi, hsi, hdx, hcx, h8, h9⟩ := ha
  refine ⟨call_rsp hu, ?_, by rw [call_gpr (by decide), hdi], by rw [call_gpr (by decide), hsi],
    by rw [call_gpr (by decide), hdx], by rw [call_gpr (by decide), hcx],
    by rw [call_gpr (by decide), h8], by rw [call_gpr (by decide), h9], h0, h1, h2, h3, h4⟩
  simp only [gkLeak, gkA, gkS, hdom, hrand, hlen, hhead, Option.toList_some]
  rfl

private theorem call_pub {q : KeyPoint} {u₁ u₂ : State} (h₁ : KeyCallCT q u₁) (h₂ : KeyCallCT q u₂) :
    attemptContract.pub (callState q.inputs q.used u₁) (callState q.inputs q.used u₂) := by
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁, g₁, i₁, j₁, k₁, l₁, m₁, n₁⟩ := call_view h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂, f₂, g₂, i₂, j₂, k₂, l₂, m₂, n₂⟩ := call_view h₂
  exact ⟨a₁.trans a₂.symm, b₁.trans b₂.symm, c₁.trans c₂.symm, d₁.trans d₂.symm, e₁.trans e₂.symm,
    f₁.trans f₂.symm, g₁.trans g₂.symm, i₁.trans i₂.symm, j₁.trans j₂.symm, k₁.trans k₂.symm,
    l₁.trans l₂.symm, m₁.trans m₂.symm, n₁.trans n₂.symm⟩

private theorem call_ready {q : KeyPoint} {u : State} (h : KeyCallCT q u) :
    attemptContract.pre (callState q.inputs q.used u) ∧
      Covers (callReads q.inputs q.used ++ callWrites q.inputs) (u.rd ++ u.wr) ∧
      Covers (callWrites q.inputs) u.wr ∧ u.gpr .rsp = q.inputs.sp - 40 := by
  obtain ⟨original, s, h, _, _, _, hr, ha, hm, k⟩ := h
  have hu : u.gpr .rsp = q.inputs.sp - 40 := by
    rw [k.gpr (by decide), allocated_rsp, h.rsp]; rfl
  exact ⟨call_attempt_pre (h.callFacts hr) h.rsp hu ha hm, call_covers_reads h hr k.2.1 k.2.2,
    call_covers_writes h k.2.2, hu⟩

theorem key_attempt_call_ct (v : RoundImpl) :
    RelCT isa (Two KeyCallCT) (attemptCall v) (fun _ _ => True) := by
  refine RelCT.callEx (attempt_correct v) (attempt_constantTime v) fun u₁ u₂ ⟨q, h₁, h₂⟩ => ?_
  obtain ⟨p₁, c₁, w₁, s₁⟩ := call_ready h₁
  obtain ⟨p₂, c₂, w₂, s₂⟩ := call_ready h₂
  exact ⟨_, _, _, _, p₁, p₂, call_pub h₁ h₂, c₁, w₁, c₂, w₂, s₁.trans s₂.symm⟩

theorem key_attempt_run_ct (v : RoundImpl) :
    RelCT isa (Two KeyReady) (attemptRun (attemptCall v)) (fun _ _ => True) := by
  unfold attemptRun
  apply frame_alloc_ct
  refine (RelCT.seq (two_piece [.r12, .rsp] key_allocated_pins (by taint_decide) arguments_ready)
    (key_attempt_call_ct v)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, h₁, h₂⟩, rfl, rfl⟩
  exact ⟨q, ⟨s, h₁, rfl⟩, ⟨t, h₂, rfl⟩⟩

end VG.Proof.Ffdh.X86_64.KeyGeneration
