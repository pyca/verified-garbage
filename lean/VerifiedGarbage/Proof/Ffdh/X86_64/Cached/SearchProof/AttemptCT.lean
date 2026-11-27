module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.CTData
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Attempt
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.AttemptRun
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.AttemptStep
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.CTData
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Attempt
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.AttemptRun
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.AttemptStep
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
public import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Search
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Exits
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Outputs
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Live
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ZeroOut
meta import VerifiedGarbage.Impl.Ffdh.X86_64.KeyGeneration.Search
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Exits
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Outputs
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Live
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ZeroOut

/-! ### `Ffdh.X86_64.Cached.SearchProof.LeafCT`, which the modules that import this one used -/

section

/-! # The key search's exits and rejections use only public addresses -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached.SearchProof

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64
open VG.Proof.Ffdh.X86_64.Generation (controller_zero_out)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

theorem key_zero_x {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hdi : s.gpr .rdi = p.control) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.zeroOut 5 2) s fun t =>
      KeyLive p original used keys scalars t ∧ t.gpr .rdi = p.control := by
  have hk := h.input.len_bounds
  have scr := h.input.control_scr (t := s) h.wr
  refine WP.mono (controller_zero_out scr hdi (by decide) (sPtr := 5) (sLen := 2) (by decide)
    (by decide) (h.header (by simp [KeyPublic.headers])) (h.header (by simp [KeyPublic.headers]))
    (by omega_using [hk]) (by omega_using [hk]) (h.input.output_x h.wr)) fun _ ⟨_, hfv, kv⟩ => ?_
  exact ⟨zero_live h h.input.x_mem h.input.x_ne_ctl hfv kv, (kv.gpr (by decide)).trans hdi⟩

def KeyZeroCT (p : KeyPublic) (s : State) : Prop := KeyAny p s ∧ s.gpr .rdi = p.control

private theorem zero_header (j : Nat) (hj : j = 5 ∨ j = 6) (p : KeyPublic) (s : State)
    (h : KeyZeroCT p s) :
    WP isa (.block [.mov .rsi (.mem (hdr j)), .mov .rcx (.mem (hdr 2)), .mov32 .rax (.imm 0)]) s
      fun t => t.gpr .rsi = (if j = 5 then p.xp else p.yp) ∧ t.gpr .rcx = BitVec.ofNat 64 p.len := by
  obtain ⟨⟨original, used, keys, scalars, h⟩, hd⟩ := h
  have scr := h.input.control_scr (t := s) h.wr
  have hk : word s.mem p.control 16 = BitVec.ofNat 64 p.len :=
    h.header (j := 2) (by simp [KeyPublic.headers])
  have hl2 : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 16) 8 := scr.ld (by decide)
  rcases hj with rfl | rfl
  · have hp : word s.mem p.control 40 = p.xp := h.header (j := 5) (by simp [KeyPublic.headers])
    have hl : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 40) 8 := scr.ld (by decide)
    xrun [State.ea, hdr, hdrOff, hd, hp, hk, hl, hl2]
  · have hp : word s.mem p.control 48 = p.yp := h.header (j := 6) (by simp [KeyPublic.headers])
    have hl : InRegions (s.rd ++ s.wr) (p.control + BitVec.ofNat 64 48) 8 := scr.ld (by decide)
    xrun [State.ea, hdr, hdrOff, hd, hp, hk, hl, hl2]

private theorem zero_ct (j : Nat) (hj : j = 5 ∨ j = 6) :
    RelCT isa (Two KeyZeroCT) (VG.Impl.Rsa.X86_64.Keys.zeroOut j 2) (fun _ _ => True) := by
  rcases hj with rfl | rfl <;> unfold VG.Impl.Rsa.X86_64.Keys.zeroOut <;>
  · refine RelCT.seq (two_piece [.rdi] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact h₁.2.trans h₂.2.symm) (by taint_decide) (zero_header _ (by decide))) ?_
    exact two_taint [.rsi, .rcx] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)

private theorem zero_ready (p : KeyPublic) (s : State) (h : KeyZeroCT p s) :
    WP isa (VG.Impl.Rsa.X86_64.Keys.zeroOut 5 2) s (KeyZeroCT p) := by
  obtain ⟨⟨original, used, keys, scalars, h⟩, hd⟩ := h
  exact WP.mono (key_zero_x h hd) fun _ ⟨ht, hdt⟩ => ⟨⟨original, used, keys, scalars, ht⟩, hdt⟩

private theorem rdi_ready (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (.block [.mov .rdi (.reg .r12)]) s (KeyZeroCT p) := by
  obtain ⟨original, used, keys, scalars, h⟩ := h
  refine WP.mono (WP.keep [.rdi] (Q := fun u => u.gpr .rdi = p.control ∧ u.mem = s.mem)
    (by xrun [h.r12]) rfl) fun _ ⟨⟨hd, hm⟩, k⟩ =>
    ⟨⟨original, used, keys, scalars, h.keep k hm (by decide)⟩, hd⟩

theorem key_zero_outputs_ct : RelCT isa (Two KeyAny) zeroOutputs (fun _ _ => True) := by
  unfold zeroOutputs
  refine RelCT.seq (two_piece [.r12, .rsp] key_any_pins (by taint_decide) rdi_ready) ?_
  exact RelCT.seq (two_post (zero_ct 5 (by decide)) zero_ready) (zero_ct 6 (by decide))

private theorem terminal_ready (status : Nat) (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (.block (terminal status)) s (KeyAny p) := by
  obtain ⟨original, used, keys, scalars, h⟩ := h
  exact WP.mono (key_terminal_live h status) fun _ ⟨ht, _⟩ => ⟨original, used, 0, 0, ht⟩

theorem key_exhausted_ct : RelCT isa (Two KeyAny) exhausted (fun _ _ => True) := by
  unfold exhausted
  exact RelCT.seq (two_piece [.r12, .rsp] key_any_pins (by taint_decide) (terminal_ready 3))
    key_zero_outputs_ct

private theorem request_ready (p : KeyPublic) (s : State) (h : KeyAny p s) :
    WP isa (.block [.mov .rax (.mem (field 2)), .store (field 3) .rax, .mov32 .rax (.imm 0),
      .store (field 14) .rax]) s (KeyAny p) := by
  obtain ⟨original, used, keys, scalars, h⟩ := h
  exact WP.mono (key_request_live h) fun _ ⟨ht, _⟩ => ⟨original, used, keys, scalars, ht⟩

theorem key_request_ct : RelCT isa (Two KeyAny) request (fun _ _ => True) := by
  unfold request
  exact RelCT.seq (two_piece [.r12, .rsp] key_any_pins (by taint_decide) request_ready)
    key_zero_outputs_ct

theorem key_accepted_ct : RelCT isa (Two KeyAny) (.block (terminal 1)) (fun _ _ => True) :=
  two_taint [.r12, .rsp] key_any_pins (by taint_decide)

theorem key_rejected_scalar_ct : RelCT isa (Two KeyAny) (.block rejectedScalar) (fun _ _ => True) :=
  two_taint [.r12, .rsp] key_any_pins (by taint_decide)

theorem key_rejected_public_ct : RelCT isa (Two KeyAny) (.block rejectedPublic) (fun _ _ => True) :=
  two_taint [.r12, .rsp] key_any_pins (by taint_decide)

end VG.Proof.Ffdh.X86_64.Cached.SearchProof

end

end

/-! # An attempt leaks only the domain and its status

The attempt's timing may depend on the domain and its status
(`attemptContract.pub`). Two runs at the same point agree on both: the
status is the first of the statuses still to come.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached.SearchProof

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Proof.Ffdh.GenerationSearch
open VG.Proof.Ffdh.X86_64.Generation (writeController allocated allocated_rsp frame_alloc_ct)
open VG.Proof.Ffdh.X86_64.Cached (cgLeak cgDom cgRand cgA cgS)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search hiding attemptRun attemptOrRequest iteration code
open VG.Impl.Ffdh.X86_64.Cached.Search

/-- A loop state at which the controller attempts a key. -/
def KeyReady (q : KeyPoint) (s : State) : Prop :=
  KeyCTL q s ∧ q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen

def KeyAllocated (q : KeyPoint) (u : State) : Prop := ∃ s, KeyReady q s ∧ u = allocated 56 s

/-- The attempt's entry, before the call. -/
def KeyCallCT (q : KeyPoint) (u : State) : Prop :=
  ∃ original s, KeyLive q.inputs original q.used q.keys q.scalars s ∧
    (q.inputs.tail (keyRand original) q.used q.keys q.scalars).statuses = q.statuses ∧
    q.keys ≠ 0 ∧ q.scalars ≠ 0 ∧ q.used + q.inputs.len ≤ q.inputs.randLen ∧
    KeyArgs q.inputs u ∧
    u.mem = writeController s.mem (s.gpr .rsp - 56) (callValues q.inputs q.used) ∧
    Keep [.rax, .rdi, .rsi, .rdx, .rcx, .r8, .r9, .r10, .r11] (allocated 56 s) u

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
    WP isa (.block cachedArguments) u (KeyCallCT q) := by
  obtain ⟨s, ⟨⟨original, h, hst⟩, hk, hs, hr⟩, rfl⟩ := h
  exact WP.mono (key_arguments_ok h) fun _ ⟨ha, hm, k⟩ => ⟨original, s, h, hst, hk, hs, hr, ha, hm, k⟩

theorem key_attempt_ready (v : RoundImpl) (q : KeyPoint) (s : State) (h : KeyReady q s) :
    WP isa (attemptRun (attemptCall v)) s (KeyAttempted q) := by
  obtain ⟨⟨original, h, hst⟩, hk, hs, hr⟩ := h
  exact WP.mono (key_attempt_run v h hr) fun _ ⟨ht, hp⟩ => ⟨original, ht, hst, hk, hs, hr, hp⟩

/-- What the attempt sees at its entry, in terms of the point alone. -/
private theorem call_view {q : KeyPoint} {u : State} (h : KeyCallCT q u) :
    (callState q.inputs q.used u).gpr .rsp = q.inputs.sp - 56 - 8 ∧
    cgLeak (callState q.inputs q.used u) = q.inputs.dom.map (·.toNat) ++ q.statuses.head?.toList ∧
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
    stackArg (callState q.inputs q.used u) 4 = BitVec.ofNat 64 (q.inputs.Z / 8) ∧
    stackArg (callState q.inputs q.used u) 5 = q.inputs.ctx ∧
    stackArg (callState q.inputs q.used u) 6 = BitVec.ofNat 64 q.inputs.ctxLen := by
  obtain ⟨original, s, h, hst, hk, hs, hr, ha, hm, k⟩ := h
  have hu : u.gpr .rsp = q.inputs.sp - 56 := by
    rw [k.gpr (by decide), allocated_rsp, h.rsp]; rfl
  have hf := h.callFacts hr
  obtain ⟨hdom, hrand, hlen, -⟩ := call_inputs h hr hf hm hu ha
  have hlen' : (keyRand original).length = q.inputs.randLen := by
    rw [← h.random]; simp only [Spec.Rsa.bytesAt, List.length_map, List.length_range]
  have hhead := keyTail_statuses_head (policy := .cached) (a := q.inputs.a) (len := q.inputs.len) (rand := keyRand original) (used := q.used)
    hk hs (by rw [hlen']; omega_using [hr])
  rw [hst] at hhead
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := call_args hu h.rsp hm
  obtain ⟨hdi, hsi, hdx, hcx, h8, h9⟩ := ha
  refine ⟨call_rsp hu, ?_, by rw [call_gpr (by decide), hdi], by rw [call_gpr (by decide), hsi],
    by rw [call_gpr (by decide), hdx], by rw [call_gpr (by decide), hcx],
    by rw [call_gpr (by decide), h8], by rw [call_gpr (by decide), h9], h0, h1, h2, h3, h4, h5, h6⟩
  simp only [cgLeak, cgA, cgS, hdom, hrand, hlen, hhead, Option.toList_some]
  rfl

private theorem call_pub {q : KeyPoint} {u₁ u₂ : State} (h₁ : KeyCallCT q u₁) (h₂ : KeyCallCT q u₂) :
    attemptContract.pub (callState q.inputs q.used u₁) (callState q.inputs q.used u₂) := by
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁, g₁, i₁, j₁, k₁, l₁, m₁, n₁, o₁, r₁⟩ := call_view h₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂, f₂, g₂, i₂, j₂, k₂, l₂, m₂, n₂, o₂, r₂⟩ := call_view h₂
  exact ⟨a₁.trans a₂.symm, b₁.trans b₂.symm, c₁.trans c₂.symm, d₁.trans d₂.symm, e₁.trans e₂.symm,
    f₁.trans f₂.symm, g₁.trans g₂.symm, i₁.trans i₂.symm, j₁.trans j₂.symm, k₁.trans k₂.symm,
    l₁.trans l₂.symm, m₁.trans m₂.symm, n₁.trans n₂.symm, o₁.trans o₂.symm, r₁.trans r₂.symm⟩

private theorem call_ready {q : KeyPoint} {u : State} (h : KeyCallCT q u) :
    attemptContract.pre (callState q.inputs q.used u) ∧
      Covers (callReads q.inputs q.used ++ callWrites q.inputs) (u.rd ++ u.wr) ∧
      Covers (callWrites q.inputs) u.wr ∧ u.gpr .rsp = q.inputs.sp - 56 := by
  obtain ⟨original, s, h, _, _, _, hr, ha, hm, k⟩ := h
  have hu : u.gpr .rsp = q.inputs.sp - 56 := by
    rw [k.gpr (by decide), allocated_rsp, h.rsp]; rfl
  exact ⟨call_pre h hr (h.callFacts hr) hm hu ha, call_covers_reads h hr k.2.1 k.2.2,
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

end VG.Proof.Ffdh.X86_64.Cached.SearchProof
