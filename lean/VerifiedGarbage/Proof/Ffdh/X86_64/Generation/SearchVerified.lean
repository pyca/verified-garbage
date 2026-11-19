module

public import VerifiedGarbage.Proof.EntropyRequest
public import VerifiedGarbage.Spec.Ffdh.SievedContract
import VerifiedGarbage.Proof.Ffdh.SievedBounds
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCTData
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Safety
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Contract
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchShort
public import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Search
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Depth
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchClassify
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCandidatePost
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRestore
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Impl.Ffdh.X86_64.Generation.Search
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchLayout
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ControlMemory
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.ControlMemory
meta import VerifiedGarbage.Proof.Framework.Omega
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchShort
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Safety
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCTData
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchClassify
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRestore
meta import VerifiedGarbage.Proof.Ffdh.Contract
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchTerminate
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchTerminate
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.AbiCorrect
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCallLayout
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.AbiCorrect
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Depth
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCallLayout
import Mathlib.Algebra.Group.Nat.Defs
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCandidatePost
meta import Mathlib.Algebra.Group.Nat.Defs

/-! ### `Ffdh.X86_64.Generation.SearchBranch`, which only this module used -/

section

/-! ### `Ffdh.X86_64.Generation.SearchCandidate`, which this module and modules that import it used -/

section

/-! # Complete internal candidate invocation, including its nested stack use -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Proof.MillerRabin.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem search_candidate_run (v : RoundImpl)
    {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) :
    WP isa (candidateRun (candidateCode v)) s fun t =>
      SearchLive p original used remaining t ∧ SearchCandidatePost p used t := by
  unfold candidateRun
  apply frame_alloc (by decide) (by decide) (by decide)
    (by
      have hs := h.input.1.2.2.2.2.2.2.2.1
      have he : s.gpr .rsp = original.gpr .rsp := by cases h.input.2; exact h.rsp
      rw [he]
      omega_using [hs])
  refine WP.seq (WP.mono (search_arguments_ok h) fun u ⟨ha, hm, k⟩ => ?_)
  have hsp : u.gpr .rsp = s.gpr .rsp - 32 := k.gpr (by decide)
  have hw := search_call_writes h k.2.2
  have hr := search_call_reads h k.2.1 k.2.2
  have hp := search_call_pre h ha hm k
  have hcorrect := pc_correct v.mont (R2Impl.words v.mont) (Kernel.called v)
    (SpSafe.of_all (candidateCode_sp v)) (candidateCode_depth v) (candidateCode_ctl v)
  refine WP.mono (inline_stack (k := pcContract) hcorrect
    (SpSafe.of_all (candidateCode_sp v)) (candidateCode_depth v) (by decide) hp
    (hr.append_left hw.right) hw) fun t ⟨htr, htw, habi, hf, hpost⟩ => ?_
  have htsp : t.gpr .rsp = u.gpr .rsp := habi.1 .rsp (by decide)
  refine ⟨?_, htw.trans k.2.2, fun m uu fm => ?_⟩
  · exact htsp.trans (k.gpr (by decide))
  · have he : s.gpr .rsp = original.gpr .rsp := by cases h.input.2; exact h.rsp
    have hR : Region.Sub ⟨s.gpr .rsp - BitVec.ofNat 64 32, 32⟩ (below (original.gpr .rsp) 160) := by
      rw [he]; exact Offset.sub_below _ (by decide) (by decide)
    have hframe := ((arguments_frame h hm).trans (call_frame h (by
      simpa only [hsp, h.rsp] using hf))).trans (fm.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), hR⟩)
    have hg : ∀ r ∈ calleeSaved, (freed 32 t).gpr r = s.gpr r := by
      intro r hr
      by_cases he : r = .rsp
      · subst he
        rw [freed_rsp, htsp, hsp]
        exact BitVec.sub_add_cancel _ _
      · rw [freed_reg _ _ _ he, habi.1 r hr, k.gpr (by cases r <;> simp_all [calleeSaved]),
          allocated_reg _ _ _ he]
    have hlive := h.restore (t := { freed 32 t with mem := m, unknowns := uu })
      (show (freed 32 t).rd = s.rd from htr.trans k.2.1)
      (show (freed 32 t).wr = s.wr from by change t.wr.tail = s.wr; rw [htw, k.2.2]; rfl) hg hframe
    have hrand := search_call_random h ha hm hsp
    have hlen : p.c.rand.length < 2 ^ 64 := by
      cases h.input.2
      simpa only [searchOfState, SearchPublic.c, candidateOfState, pcRand, Spec.Rsa.bytesAt,
        List.length_map, List.length_range] using (stackArg original 0).isLt
    have ha0 : stackArg u 0 = BitVec.ofNat 64 (p.c.rand.length - used) :=
      search_call_args hsp hm 0 (by decide)
    have hl : (stackArg u 0).toNat = p.c.rand.length - used := by
      rw [ha0, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hlen])]
    have hout : SearchCandidatePost p used t := search_candidate_post h.input ha hrand hl hpost
    exact ⟨hlive, SearchCandidatePost.lost h.input hout (freed_reg 32 t .rax (by decide)) fm hR⟩

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! # Public control-state transitions for paired native search executions -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Impl.Ffdh.X86_64.Generation.Search

def SearchRemainingGuard (p : SearchPoint) (s : State) : Prop := SearchCTL p s ∧
  eval .e s = some (decide (p.remaining = 0))

def SearchBranchResult (p : SearchPoint) (s : State) : Prop :=
  if p.remaining = 0 then ∃ original, SearchDone p.inputs original (.exhausted p.used) s
  else ∃ original, SearchClassified p.inputs original p.used p.remaining s

theorem remaining_ready (p : SearchPoint) (s : State) (h : SearchCTL p s) :
    WP isa (.block [.mov .rax (.mem (field 0)), .alu .test .rax (.reg .rax)]) s
      (SearchRemainingGuard p) := by
  obtain ⟨original, h⟩ := h
  exact WP.mono (remaining_guard h) fun _ ⟨ht, he⟩ => ⟨⟨original, ht⟩, he⟩

theorem candidate_ready (v : RoundImpl) (p : SearchPoint) (s : State) (h : SearchCTL p s) :
    WP isa (candidateRun (candidateCode v)) s (SearchCandidateCT p) := by
  obtain ⟨original, h⟩ := h
  exact WP.mono (search_candidate_run v h) fun _ ⟨ht, hp⟩ => ⟨original, ht, hp⟩

theorem branch_ready (v : RoundImpl) (p : SearchPoint) (s : State) (h : SearchRemainingGuard p s) :
    WP isa (.ite .e exhausted (.seq (candidateRun (candidateCode v)) classify)) s (SearchBranchResult p) := by
  obtain ⟨⟨original, hl⟩, he⟩ := h
  refine WP.ite (decide (p.remaining = 0)) he ?_ ?_
  · intro hz
    change WP isa exhausted s (fun t => SearchBranchResult p t)
    simp only [SearchBranchResult, of_decide_eq_true hz, ite_true]
    exact WP.mono (search_exhausted hl) fun _ ht => ⟨original, ht⟩
  · intro hnz
    change WP isa (.seq _ _) s (fun t => SearchBranchResult p t)
    simp only [SearchBranchResult, of_decide_eq_false hnz, ite_false]
    refine WP.seq (WP.mono (search_candidate_run v hl) fun t ⟨ht, hp⟩ => ?_)
    exact WP.mono (search_classify ht (by omega_using [of_decide_eq_false hnz]) hp) fun _ hq => ⟨original, hq⟩

theorem branch_result_r12 {p : SearchPoint} {s : State} (h : SearchBranchResult p s) :
    s.gpr .r12 = p.inputs.control := by
  by_cases hr : p.remaining = 0
  · simp only [SearchBranchResult, hr, ite_true] at h
    obtain ⟨_, h⟩ := h
    exact h.r12
  · simp only [SearchBranchResult, hr, ite_false] at h
    obtain ⟨original, h⟩ := h
    cases hc : searchCandidate p.inputs p.used with
    | none => simp only [SearchClassified, hc] at h; exact h.r12
    | some pair =>
      obtain ⟨value, rest⟩ := pair
      cases value with
      | none => simp only [SearchClassified, hc] at h; exact h.1.r12
      | some prime => simp only [SearchClassified, hc] at h; exact h.r12

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! ### `Ffdh.X86_64.Generation.SearchCallCT`, which only this module used -/

section

/-! # Internal candidate calls retain the existing public-tape timing contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem search_arguments_ready (p : SearchPoint) (s : State) (h : SearchAllocated p s) :
    WP isa (.block arguments) s (SearchCallCT p) := by
  obtain ⟨original, before, h, rfl⟩ := h
  refine WP.mono (search_arguments_ok h) fun t ⟨ha, hm, k⟩ => ?_
  have hsp : t.gpr .rsp = before.gpr .rsp - 32 := k.gpr (by decide)
  have hw := search_call_writes h k.2.2
  exact ⟨⟨search_call_pre h ha hm k, (search_call_reads h k.2.1 k.2.2).append_left hw.right, hw⟩,
    ha, by rw [hsp, h.rsp], search_call_random h ha hm hsp,
    search_call_args hsp hm 0 (by decide), search_call_args hsp hm 1 (by decide),
    search_call_args hsp hm 2 (by decide)⟩

private theorem call_pub {p : SearchPoint} {s t : State} (h₁ : SearchCallCT p s) (h₂ : SearchCallCT p t) :
    pcPub (s.withRegions (callReads p.inputs p.used) (callWrites p.inputs))
      (t.withRegions (callReads p.inputs p.used) (callWrites p.inputs)) := by
  obtain ⟨_, ⟨a₁, b₁, c₁, d₁, e₁, f₁⟩, sp₁, rand₁, n₁, scr₁, len₁⟩ := h₁
  obtain ⟨_, ⟨a₂, b₂, c₂, d₂, e₂, f₂⟩, sp₂, rand₂, n₂, scr₂, len₂⟩ := h₂
  exact ⟨sp₁.trans sp₂.symm, by change (pcRand s).map (·.toNat) = (pcRand t).map (·.toNat); rw [rand₁, rand₂],
    a₁.trans a₂.symm, b₁.trans b₂.symm, c₁.trans c₂.symm, d₁.trans d₂.symm,
    congrArg (BitVec.setWidth 32) (e₁.trans e₂.symm), f₁.trans f₂.symm,
    n₁.trans n₂.symm, scr₁.trans scr₂.symm, len₁.trans len₂.symm⟩

theorem search_candidate_inline_ct (v : RoundImpl) :
    RelCT isa (Two SearchCallCT) (candidateCode v) (fun _ _ => True) := by
  intro s₁ s₂ tr₁ tr₂ t₁ t₂ ⟨p, h₁, h₂⟩ he₁ he₂
  have hc := pc_correct v.mont (R2Impl.words v.mont) (Kernel.called v)
    (SpSafe.of_all (candidateCode_sp v)) (candidateCode_depth v) (candidateCode_ctl v)
  have ct := inline_constantTime (k := pcContract)
    (fun s h => by obtain ⟨tr, t, he, _, _⟩ := hc s h; exact ⟨tr, t, he⟩)
    (pc_constantTime v.mont (R2Impl.words v.mont) (Kernel.called v))
    (fun _ => callReads p.inputs p.used) (fun _ => callWrites p.inputs)
  exact ⟨ct _ _ _ _ _ _ h₁.1 h₂.1 (call_pub h₁ h₂) he₁ he₂, trivial⟩

theorem search_candidate_run_ct (v : RoundImpl) :
    RelCT isa (Two SearchCTL) (candidateRun (candidateCode v)) (fun _ _ => True) := by
  unfold candidateRun
  apply frame_alloc_ct
  refine (RelCT.seq (two_piece [.r12, .rsp] search_allocated_pins (by taint_decide)
    search_arguments_ready) (search_candidate_inline_ct v)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨p, ⟨o₁, h₁⟩, ⟨o₂, h₂⟩⟩, rfl, rfl⟩
  exact ⟨p, ⟨o₁, s, h₁, rfl⟩, ⟨o₂, t, h₂, rfl⟩⟩

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! ### `Ffdh.X86_64.Generation.SearchShortCT`, which only this module used -/

section

/-! ### `Ffdh.X86_64.Generation.SearchClearCT`, which this module and modules that import it used -/

section

/-! # Native failure clearing leaks only the public output pointer and width -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

def SearchZeroCT (p : SearchPoint) (s : State) : Prop := SearchCTL p s ∧ s.gpr .rdi = p.inputs.control

private theorem zero_header (p : SearchPoint) (s : State) (h : SearchZeroCT p s) :
    WP isa (.block [.mov .rsi (.mem (hdr 5)), .mov .rcx (.mem (hdr 6)), .mov32 .rax (.imm 0)]) s
      fun t => t.gpr .rsi = p.inputs.c.op ∧ t.gpr .rcx = BitVec.ofNat 64 p.inputs.c.k := by
  obtain ⟨⟨original, h⟩, hd⟩ := h
  have scr := h.input.control_scr h.wr
  have hp : word s.mem p.inputs.control 40 = p.inputs.c.op :=
    h.headers (5, p.inputs.c.op) (by simp [SearchPublic.headers])
  have hk : word s.mem p.inputs.control 48 = BitVec.ofNat 64 p.inputs.c.k :=
    h.headers (6, BitVec.ofNat 64 p.inputs.c.k) (by simp [SearchPublic.headers])
  have hl5 : InRegions (s.rd ++ s.wr) (p.inputs.control + BitVec.ofNat 64 40) 8 := scr.ld (by decide)
  have hl6 : InRegions (s.rd ++ s.wr) (p.inputs.control + BitVec.ofNat 64 48) 8 := scr.ld (by decide)
  xrun [State.ea, hdr, hdrOff, hd, hp, hk, hl5, hl6]

theorem search_zero_ct : RelCT isa (Two SearchZeroCT) (VG.Impl.Rsa.X86_64.Keys.zeroOut 5 6)
    (fun _ _ => True) := by
  unfold VG.Impl.Rsa.X86_64.Keys.zeroOut
  refine RelCT.seq (two_piece [.rdi] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_singleton] at hr
    subst r
    exact h₁.2.trans h₂.2.symm) (by taint_decide) zero_header) ?_
  exact two_taint [.rsi, .rcx] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)

private theorem exhausted_prefix (p : SearchPoint) (s : State) (h : SearchCTL p s) :
    WP isa (.block (terminal 3 ++ ([.mov .rdi (.reg .r12)] : List Instr))) s
      (SearchZeroCT { p with remaining := 0 }) := by
  obtain ⟨original, h⟩ := h
  rw [WP.block_append_iff]
  refine WP.mono (search_terminal h 3) fun t ⟨ht, _, _⟩ => ?_
  refine WP.mono (WP.keep [.rdi] (Q := fun u =>
    u.gpr .rdi = p.inputs.control ∧ u.mem = t.mem) (by xrun [ht.r12]) rfl)
    fun u ⟨⟨hd, hm⟩, k⟩ => ⟨⟨original, ht.keep k hm (by decide)⟩, hd⟩

theorem search_exhausted_ct : RelCT isa (Two SearchCTL) exhausted (fun _ _ => True) := by
  unfold exhausted
  exact RelCT.seq (two_piece [.r12, .rsp] search_ctl_pins (by taint_decide) exhausted_prefix)
    (two_map (fun p => { p with remaining := 0 }) (fun _ _ h => h) search_zero_ct)

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! ### `Ffdh.X86_64.Generation.SearchLeafCT`, which this module and modules that import it used -/

section

/-! # Native acceptance and rejection use only public memory addresses -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

def UsedPins (p : SearchPoint) (s : State) : Prop := s.gpr .rax = p.inputs.c.up ∧ s.gpr .r12 = p.inputs.control

private theorem used_pointer (p : SearchPoint) (s : State) (h : SearchCTL p s) :
    WP isa (.block [.mov .rax (.mem (field 7))]) s (UsedPins p) := by
  obtain ⟨original, h⟩ := h
  have scr := h.input.control_scr h.wr
  have hl : InRegions (s.rd ++ s.wr) (p.inputs.control + BitVec.ofNat 64 56) 8 := scr.ld (by decide)
  have hp : word s.mem p.inputs.control 56 = p.inputs.c.up :=
    h.headers (7, p.inputs.c.up) (by simp [SearchPublic.headers])
  refine WP.mono (WP.keep [.rax] (Q := fun t => t.gpr .rax = p.inputs.c.up)
    (by xrun [State.ea, field, off, h.r12, hl, hp, BitVec.ofInt_natCast, Nat.reduceMul]) rfl)
    fun _ ⟨ha, k⟩ => ⟨ha, (k.gpr (by decide)).trans h.r12⟩

private theorem used_pins : Pins UsedPins [.rax, .r12] := by
  intro p s t h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]

private theorem used_pointer_ct : RelCT isa (Two SearchCTL) (.block [.mov .rax (.mem (field 7))])
    (Two UsedPins) := two_piece [.r12, .rsp] search_ctl_pins (by taint_decide) used_pointer

theorem search_accept_ct : RelCT isa (Two SearchCTL) (.block accept) (fun _ _ => True) := by
  change RelCT isa (Two SearchCTL) (.block ([.mov .rax (.mem (field 7))] ++ accept.drop 1)) _
  exact RelCT.block_append (RelCT.seq used_pointer_ct (two_taint [.rax, .r12] used_pins (by taint_decide)))

theorem search_reject_ct : RelCT isa (Two SearchCTL) (.block reject) (fun _ _ => True) := by
  change RelCT isa (Two SearchCTL) (.block ([.mov .rax (.mem (field 7))] ++ reject.drop 1)) _
  exact RelCT.block_append (RelCT.seq used_pointer_ct (two_taint [.rax, .r12] used_pins (by taint_decide)))

theorem search_request_ct : RelCT isa (Two SearchCTL) (.block request) (fun _ _ => True) :=
  two_taint [.r12, .rsp] search_ctl_pins (by taint_decide)

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! # The native refill/exhaustion decision depends only on public policy -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

def SearchShortGuard (p : SearchPoint) (s : State) : Prop := SearchCTL p s ∧
  eval .ae s = some (decide (Spec.Ffdh.parameterEntropy p.inputs.c.bits ≤ p.inputs.c.rand.length - p.used))

private theorem short_guard_ready (p : SearchPoint) (s : State) (h : SearchCTL p s) :
    WP isa (.block [.mov .rax (.mem (field 11)), .alu .cmp .rax (.mem (field 2))]) s
      (SearchShortGuard p) := by
  obtain ⟨original, h⟩ := h
  exact WP.mono (short_guard h) fun t ⟨ht, _, _, he⟩ => ⟨⟨original, ht⟩, he⟩

theorem search_short_ct : RelCT isa (Two SearchCTL) short (fun _ _ => True) := by
  unfold short
  refine RelCT.seq (two_piece [.r12, .rsp] search_ctl_pins (by taint_decide) short_guard_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · exact search_exhausted_ct.mono (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1.1, h₂.1.1⟩) (fun _ _ h => h)
  · exact search_request_ct.mono (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1.1, h₂.1.1⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! ### `Ffdh.X86_64.Generation.SearchIterationCT`, which only this module used -/

section

/-! ### `Ffdh.X86_64.Generation.SearchClassifyCT`, which only this module used -/

section

/-! # Candidate classification leaks only its public-tape result -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

def SearchFirstGuard (p : SearchPoint) (s : State) : Prop := SearchCTL p s ∧
  s.gpr .rax = BitVec.ofNat 64 (Proof.Ffdh.candidateStatus (searchCandidate p.inputs p.used)) ∧
  eval .e s = some (decide (Proof.Ffdh.candidateStatus (searchCandidate p.inputs p.used) = 1))

def SearchSecondGuard (p : SearchPoint) (s : State) : Prop := SearchCTL p s ∧
  eval .e s = some (decide (Proof.Ffdh.candidateStatus (searchCandidate p.inputs p.used) = 2))

private theorem first_guard_ready (p : SearchPoint) (s : State) (h : SearchCandidateCT p s) :
    WP isa (.block [.mov32 .rax (.reg .rax), .alu .cmp .rax (.imm 1)]) s (SearchFirstGuard p) := by
  obtain ⟨original, h, hp⟩ := h
  refine WP.mono (candidate_status_guard s) fun t ⟨⟨he, ha, hm⟩, k⟩ => ?_
  exact ⟨⟨original, h.keep k hm (by decide)⟩, normalized_status hp.1 ha, by rw [hp.1] at he; exact he⟩

private theorem second_guard_ready (p : SearchPoint) (s : State) (h : SearchFirstGuard p s) :
    WP isa (.block [.alu .cmp .rax (.imm 2)]) s (SearchSecondGuard p) := by
  obtain ⟨⟨original, hl⟩, ha, _⟩ := h
  have hb : Proof.Ffdh.candidateStatus (searchCandidate p.inputs p.used) < 2 ^ 64 := by
    cases hc : searchCandidate p.inputs p.used with
    | none => decide
    | some pair =>
      obtain ⟨value, rest⟩ := pair
      cases value <;> dsimp only [Proof.Ffdh.candidateStatus] <;> decide
  exact WP.mono (second_status_guard ha hb) fun _ ⟨⟨he, hm⟩, k⟩ =>
    ⟨⟨original, hl.keep k hm (by decide)⟩, he⟩

theorem search_classify_ct : RelCT isa (Two SearchCandidateCT) classify (fun _ _ => True) := by
  unfold classify
  refine RelCT.seq (two_piece [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide) first_guard_ready) ?_
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.2.trans h₂.2.2.symm) ?_ ?_
  · exact search_accept_ct.mono (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1.1, h₂.1.1⟩) (fun _ _ h => h)
  · refine RelCT.seq (R := Two SearchSecondGuard) ?_ ?_
    · exact (two_piece [] (fun _ _ _ _ _ _ h => by cases h) (by taint_decide) second_guard_ready).mono
        (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1, h₂.1⟩) (fun _ _ h => h)
    · refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
      · exact search_reject_ct.mono (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1.1, h₂.1.1⟩) (fun _ _ h => h)
      · exact search_short_ct.mono (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1.1, h₂.1.1⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! # Constant-time native search iterations, including internal candidate calls -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Impl.Ffdh.X86_64.Generation.Search

private theorem branch_ct (v : RoundImpl) :
    RelCT isa (Two SearchRemainingGuard)
      (.ite .e exhausted (.seq (candidateRun (candidateCode v)) classify)) (fun _ _ => True) := by
  refine two_ite (fun _ _ _ h₁ h₂ => h₁.2.trans h₂.2.symm) ?_ ?_
  · exact search_exhausted_ct.mono (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1.1, h₂.1.1⟩) (fun _ _ h => h)
  · exact (RelCT.seq (two_post (search_candidate_run_ct v) (candidate_ready v)) search_classify_ct).mono
      (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.1.1, h₂.1.1⟩) (fun _ _ h => h)

theorem search_iteration_ct (v : RoundImpl) :
    RelCT isa (Two SearchCTL) (iteration (candidateCode v)) (fun _ _ => True) := by
  unfold iteration
  change RelCT isa _ (.seq _ (.seq _ _)) _
  refine RelCT.seq (two_piece [.r12, .rsp] search_ctl_pins (by taint_decide) remaining_ready) ?_
  exact RelCT.seq (two_post (branch_ct v) (branch_ready v))
    (two_taint [.r12] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact (branch_result_r12 h₁).trans (branch_result_r12 h₂).symm) (by taint_decide))

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! ### `Ffdh.X86_64.Generation.SearchFinishCT`, which only this module used -/

section

/-! # Returning a native search does not expose private saved register values -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search VG.Proof.MlKem.X86_64

structure SearchEndPoint where
  inputs : SearchPublic
  result : Spec.Ffdh.ParameterSearchResult

def SearchCTDone (p : SearchEndPoint) (s : State) : Prop :=
  ∃ original, SearchDone p.inputs original p.result s

private theorem finish_pointer (p : SearchEndPoint) (s : State) (h : SearchCTDone p s) :
    WP isa (.block (finish.take 4)) s fun t => t.gpr .rdx = p.inputs.c.up := by
  obtain ⟨original, h⟩ := h
  have scr := h.input.control_scr h.wr
  have hl : ∀ d, d + 8 ≤ 128 → InRegions (s.rd ++ s.wr) (p.inputs.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.ld hd
  unfold finish
  simp only [List.take_succ_cons, List.take_zero]
  xrun [State.ea, field, off, h.r12, h.usedPtr, Nat.reduceMul, BitVec.ofInt_natCast,
    hl 56 (by decide), hl 96 (by decide), hl 112 (by decide), hl 32 (by decide)]

theorem search_finish_ct : RelCT isa (Two SearchCTDone) (.block finish) (fun _ _ => True) := by
  change RelCT isa (Two SearchCTDone) (.block (finish.take 4 ++ finish.drop 4)) _
  refine RelCT.block_append (RelCT.seq (two_piece [.r12] ?_ (by taint_decide) finish_pointer) ?_)
  · intro p s t ⟨_, h₁⟩ ⟨_, h₂⟩ r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h₁.r12.trans h₂.r12.symm
  · exact two_taint [.rdx] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact h₁.trans h₂.symm) (by taint_decide)

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! ### `Ffdh.X86_64.Generation.SearchEntryCT`, which only this module used -/

section

/-! ### `Ffdh.X86_64.Generation.SearchEntry`, which this module and modules that import it used -/

section

/-! # Capture register arguments before loading the stack arguments -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

def searchHeadValues (s : State) : List (Nat × BitVec 64) :=
  [(4, s.gpr .r12), (5, s.gpr .rdi), (6, s.gpr .rsi), (7, s.gpr .rdx),
    (8, s.gpr .rcx), (9, ((s.gpr .r8).setWidth 32).setWidth 64), (10, s.gpr .r9)]

def searchTailValues (s : State) : List (Nat × BitVec 64) :=
  [(11, stackArg s 0), (13, stackArg s 1), (15, stackArg s 2), (12, 0)]

def searchEntryValues (s : State) : List (Nat × BitVec 64) := searchHeadValues s ++ searchTailValues s

theorem searchHeadValues_bound (s : State) : ∀ e ∈ searchHeadValues s, e.1 < 16 := by
  simp only [searchHeadValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem searchTailValues_bound (s : State) : ∀ e ∈ searchTailValues s, e.1 < 16 := by
  simp only [searchTailValues, List.mem_cons, List.not_mem_nil, or_false]
  rintro _ (rfl | rfl | rfl | rfl) <;> dsimp only <;> decide

theorem input_arg_contains (s : State) {j : Nat} (hj : j < 4) :
    (inputArgs s).Contains (stackArgAddr s j) 8 := by
  rw [show stackArgAddr s j = stackArgAddr s 0 + BitVec.ofNat 64 (8 * j) by
    simp only [stackArgAddr, Nat.zero_add, Nat.mul_one, Offset.add_add]
    congr 2
    omega_using [hj]]
  exact Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj])

theorem input_args {p : SearchPublic} {s : State} (h : SearchInput p s) :
    ∀ j < 4, InRegions (s.rd ++ s.wr) (stackArgAddr s j) 8 := by
  intro j hj
  refine ⟨inputArgs s, ?_, input_arg_contains s hj⟩
  rw [h.1.2.2.1]
  exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))

theorem search_entry_head_ok {p : SearchPublic} {s : State} (h : SearchInput p s) :
    WP isa (.block entryHead) s fun t =>
      t.gpr .r12 = p.control ∧
      t.mem = writeController s.mem p.control (searchHeadValues s) ∧
      Keep [.rax, .r8, .r12] s t := by
  have scr := h.control_scr (s := s) rfl
  have hd : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 32) 64 = p.control := congrArg SearchPublic.control h.2
  have hs : ∀ d, d + 8 ≤ 128 → InRegions s.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have ha : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 32) 8 := input_args h 3 (by decide)
  refine WP.mono (WP.keep [.rax, .r8, .r12] (Q := fun t =>
    t.gpr .r12 = p.control ∧ t.mem = writeController s.mem p.control (searchHeadValues s)) ?_ rfl)
    fun _ ⟨⟨hr, hm⟩, k⟩ => ⟨hr, hm, k⟩
  unfold entryHead writeController searchHeadValues
  simp only [List.foldl_cons, List.foldl_nil]
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul, hd, ha,
    hs 32 (by decide), hs 40 (by decide), hs 48 (by decide), hs 56 (by decide),
    hs 64 (by decide), hs 72 (by decide), hs 80 (by decide)]

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! # Native search entry exposes pointers and public policy, never saved registers -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

private theorem entry_pointer (p : SearchPublic) (s : State) (h : SearchInput p s) :
    WP isa (.block (entryHead.take 2)) s fun t => t.gpr .rax = p.control := by
  have hd : s.mem.readW (s.gpr .rsp + BitVec.ofNat 64 32) 64 = p.control :=
    congrArg SearchPublic.control h.2
  have ha : InRegions (s.rd ++ s.wr) (s.gpr .rsp + BitVec.ofNat 64 32) 8 := input_args h 3 (by decide)
  unfold entryHead
  simp only [List.take_succ_cons, List.take_zero]
  xrun [State.ea, BitVec.ofInt_ofNat, hd, ha]

private theorem entry_head_ct : RelCT isa (Two SearchInput) (.block entryHead) (fun _ _ => True) := by
  change RelCT isa (Two SearchInput) (.block (entryHead.take 2 ++ entryHead.drop 2)) _
  refine RelCT.block_append (RelCT.seq (two_piece [.rsp] ?_ (by taint_decide) entry_pointer) ?_)
  · intro p s t h₁ h₂ r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact (congrArg (fun q => q.c.sp) h₁.2).trans (congrArg (fun q => q.c.sp) h₂.2).symm
  · exact two_taint [.rax] (fun _ _ _ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr
      subst r
      exact h₁.trans h₂.symm) (by taint_decide)

def SearchEntryPins (p : SearchPublic) (s : State) : Prop := s.gpr .r12 = p.control ∧ s.gpr .rsp = p.c.sp

private theorem entry_head_pins (p : SearchPublic) (s : State) (h : SearchInput p s) :
    WP isa (.block entryHead) s (SearchEntryPins p) := by
  refine WP.mono (search_entry_head_ok h) fun t ⟨hr, _, k⟩ => ⟨hr, ?_⟩
  exact (k.gpr (by decide)).trans (congrArg (fun q => q.c.sp) h.2)

theorem search_entry_ct : RelCT isa (Two SearchInput) (.block entry) (fun _ _ => True) := by
  unfold entry
  refine RelCT.block_append (RelCT.seq (two_post entry_head_ct entry_head_pins) ?_)
  exact two_taint [.r12, .rsp] (fun _ _ _ h₁ h₂ r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    exacts [h₁.1.trans h₂.1.symm, h₁.2.trans h₂.2.symm]) (by taint_decide)

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! ### `Ffdh.X86_64.Generation.SearchStart`, which only this module used -/

section

/-! # Establish the complete parameter-search invariant -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/SearchEntryTail.lean`, which only this module imported.
section

/-! # Capture stack arguments without changing the caller's argument area -/

section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem search_entry_head_args {p : SearchPublic} {s : State} (h : SearchInput p s)
    {t : State} (hm : t.mem = writeController s.mem p.control (searchHeadValues s))
    (k : Keep [.rax, .r8, .r12] s t) (j : Nat) (hj : j < 4) :
    stackArg t j = stackArg s j := by
  have hf := writeController_frame s.mem p.control (searchHeadValues s) (searchHeadValues_bound s)
  have hd : (inputArgs s).Disjoint ⟨p.control, 128⟩ := by
    cases h.2
    exact (h.1.2.2.2.2.2.1 _ (by simp)).symm
  change t.mem.readW (stackArgAddr t j) 64 = _
  have ha : stackArgAddr t j = stackArgAddr s j := by
    simp only [stackArgAddr, k.1 .rsp (by simp)]
  rw [ha, hm]
  exact hf.readW (input_arg_contains s hj) (fun r hr => by
    obtain rfl := List.mem_singleton.mp hr
    exact hd) (by decide)

theorem search_entry_tail_ok {p : SearchPublic} {s t : State} (h : SearchInput p s)
    (hm : t.mem = writeController s.mem p.control (searchHeadValues s))
    (k : Keep [.rax, .r8, .r12] s t) (hr : t.gpr .r12 = p.control) :
    WP isa (.block entryTail) t fun u =>
      u.mem = writeController t.mem p.control (searchTailValues s) ∧
      Keep [.rax, .r10, .r11] t u := by
  have scr := h.control_scr (s := t) k.2.2
  have hs : ∀ d, d + 8 ≤ 128 → InRegions t.wr (p.control + BitVec.ofNat 64 d) 8 :=
    fun _ hd => scr.st hd
  have ha (j : Nat) (hj : j < 4) : InRegions (t.rd ++ t.wr) (stackArgAddr t j) 8 := by
    simpa only [k.2.1, k.2.2, stackArgAddr, k.1 .rsp (by simp)] using input_args h j hj
  have hv (j : Nat) (hj : j < 4) : t.mem.readW (stackArgAddr t j) 64 = stackArg s j :=
    search_entry_head_args h hm k j hj
  refine WP.keep [.rax, .r10, .r11] ?_ rfl
  unfold entryTail writeController searchTailValues
  simp only [List.foldl_cons, List.foldl_nil]
  have ha0 : InRegions (t.rd ++ t.wr) (t.gpr .rsp + BitVec.ofNat 64 8) 8 := ha 0 (by decide)
  have ha1 : InRegions (t.rd ++ t.wr) (t.gpr .rsp + BitVec.ofNat 64 16) 8 := ha 1 (by decide)
  have ha2 : InRegions (t.rd ++ t.wr) (t.gpr .rsp + BitVec.ofNat 64 24) 8 := ha 2 (by decide)
  have hv0 : t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 8) 64 = stackArg s 0 := hv 0 (by decide)
  have hv1 : t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 16) 64 = stackArg s 1 := hv 1 (by decide)
  have hv2 : t.mem.readW (t.gpr .rsp + BitVec.ofNat 64 24) 64 = stackArg s 2 := hv 2 (by decide)
  xrun [State.ea, field, off, BitVec.ofInt_ofNat, BitVec.ofInt_natCast, Nat.reduceMul,
    hr, ha0, ha1, ha2, hv0, hv1, hv2, hs 88 (by decide), hs 104 (by decide),
    hs 120 (by decide), hs 96 (by decide)]
  rfl

theorem search_entry_ok {p : SearchPublic} {s : State} (h : SearchInput p s) :
    WP isa (.block entry) s fun t =>
      t.gpr .r12 = p.control ∧
      t.mem = writeController s.mem p.control (searchEntryValues s) ∧
      Keep [.rax, .r8, .r12, .r10, .r11] s t := by
  rw [entry, WP.block_append_iff]
  refine WP.mono (search_entry_head_ok h) fun t ⟨hr, hm, k⟩ => ?_
  refine WP.mono (search_entry_tail_ok h hm k hr) fun u ⟨hu, ku⟩ => ?_
  exact ⟨(ku.gpr (by decide)).trans hr,
    by rw [hu, hm, searchEntryValues, writeController_append],
    (k.trans ku).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.Generation
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Ffdh.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem searchEntryValues_bound (s : State) : ∀ e ∈ searchEntryValues s, e.1 < 16 := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact searchHeadValues_bound s e he
  · exact searchTailValues_bound s e he

theorem search_entry_headers {p : SearchPublic} {s : State} (h : SearchInput p s) :
    Slots (writeController s.mem p.control (searchEntryValues s)) p.control (p.headers 0 p.remaining) := by
  cases h.2
  have hlen : (pcRand s).length = (stackArg s 0).toNat := by
    simp only [pcRand, Spec.Rsa.bytesAt, List.length_map, List.length_range]
  have hwidth : BitVec.ofNat 64 ((s.gpr .r8).setWidth 32).toNat =
      ((s.gpr .r8).setWidth 32).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  intro e he
  simp only [SearchPublic.headers, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [writeController_word _ _ _ (searchEntryValues_bound s) _ (by dsimp only; decide)] <;>
    simp only [searchOfState, candidateOfState, SearchPublic.c, controllerValue,
      searchEntryValues, searchHeadValues, searchTailValues, List.foldl_append,
      List.foldl_cons, List.foldl_nil, Nat.reduceEqDiff, ite_true, ite_false,
      Nat.sub_zero, Nat.mul_zero, off, BitVec.add_zero, BitVec.ofNat_toNat,
      hwidth, hlen, BitVec.setWidth_eq]
  · simp only [Bignum.word, off, BitVec.add_zero]
  · exact h.1.2.2.2.2.2.2.2.2.2.2.1
  · exact h.1.2.2.2.2.2.2.2.2.2.2.2.1
  · rfl
  · rw [Nat.mul_div_cancel _ (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem search_start {p : SearchPublic} {s : State} (h : SearchInput p s) :
    WP isa (.block entry) s fun t => SearchLive p s 0 p.remaining t := by
  refine WP.mono (search_entry_ok h) fun t ⟨hr, hm, k⟩ => ?_
  have hf := writeController_frame s.mem p.control (searchEntryValues s) (searchEntryValues_bound s)
  refine ⟨h, by omega_using [], by omega_using [], k.2.1, k.2.2, ?_, hr, ?_, ?_, ?_, ?_⟩
  · cases h.2
    exact k.gpr (by decide)
  · intro r hcal hne
    exact k.gpr (by cases r <;> simp_all [calleeSaved])
  · rw [hm]
    change word (writeController s.mem p.control (searchEntryValues s)) p.control (8 * 4) = _
    rw [writeController_word _ _ _ (searchEntryValues_bound s) 4 (by decide)]
    rfl
  · have hf' : Frame (s.wr ++ [below (s.gpr .rsp) 160]) s.mem t.mem := by
      rw [hm]
      exact hf.sub fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact ⟨inputControl s, List.mem_append_left _ (by rw [h.1.2.2.2.1]; simp), by
          cases h.2; exact fun _ hi => hi⟩
    rw [h.random_frame hf']
    cases h.2
    dsimp only [searchOfState, SearchPublic.c, candidateOfState]
    simp only [pcRand, Spec.Rsa.bytesAt, List.length_map, List.length_range]
  · rw [hm]
    exact search_entry_headers h

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! ### `Ffdh.X86_64.Generation.SearchLoop`, which only this module used -/

section

/-! ### `Ffdh.X86_64.Generation.SearchLoopGuards`, which this module and modules that import it used -/

section

/-! # Only a native rejection continues the search loop -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem done_loop_guard {p : SearchPublic} {original s : State} {result : Spec.Ffdh.ParameterSearchResult}
    (h : SearchDone p original result s) :
    WP isa (.block [.mov .rax (.mem (field 14)), .alu .cmp .rax (.imm 4)]) s fun t =>
      eval .e t = some false ∧ SearchDone p original result t := by
  have hb : result.status < 2 ^ 64 := by cases result <;> dsimp only [Spec.Ffdh.ParameterSearchResult.status] <;> decide
  refine WP.mono (loop_guard (h.input.control_scr h.wr) h.r12 h.status hb)
    fun t ⟨⟨he, hm⟩, k⟩ => ?_
  refine ⟨?_, h.keep k hm (by decide)⟩
  cases result <;> exact he

theorem live_loop_guard {p : SearchPublic} {original s : State} {used remaining : Nat}
    (h : SearchLive p original used remaining s) (hs : word s.mem p.control 112 = 4) :
    WP isa (.block [.mov .rax (.mem (field 14)), .alu .cmp .rax (.imm 4)]) s fun t =>
      eval .e t = some true ∧ SearchLive p original used remaining t := by
  refine WP.mono (loop_guard (status := 4) (h.input.control_scr h.wr) h.r12 hs (by decide))
    fun _ ⟨⟨he, hm⟩, k⟩ => ⟨he, h.keep k hm (by decide)⟩

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! ### `Ffdh.X86_64.Generation.SearchSemantics`, which this module and modules that import it used -/

section

/-! # The native controller's local transitions implement the complete search -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.Proof.Ffdh.SievedGeneration

def searchTail (p : SearchPublic) (used remaining : Nat) : Spec.Ffdh.ParameterSearchResult :=
  (Spec.Ffdh.sievedParameterSearch p.c.bits p.c.gen remaining (p.c.rand.drop used)).consume used

theorem searchTail_zero (p : SearchPublic) (used : Nat) : searchTail p used 0 = .exhausted used := rfl

theorem searchTail_short {p : SearchPublic} {used remaining : Nat} (hr : 0 < remaining)
    (hc : searchCandidate p used = none) : searchTail p used remaining = shortResult p used remaining := by
  cases remaining with
  | zero => omega_using [hr]
  | succ n =>
    unfold searchTail
    rw [Spec.Ffdh.sievedParameterSearch, show Spec.Ffdh.sievedParameterCandidate p.c.bits p.c.gen
      (p.c.rand.drop used) = none from hc]
    simp only [List.length_drop]
    by_cases hb : Spec.Ffdh.parameterEntropy p.c.bits ≤ p.c.rand.length - used <;>
      simp [hb, shortResult, Spec.Ffdh.ParameterSearchResult.consume]

theorem searchTail_accept {p : SearchPublic} {used remaining prime : Nat} {rest : List Byte}
    (hr : 0 < remaining) (hc : searchCandidate p used = some (some prime, rest)) :
    searchTail p used remaining = .accepted prime (used + (p.c.rand.length - used - rest.length)) := by
  cases remaining with
  | zero => omega_using [hr]
  | succ n =>
    unfold searchTail
    rw [Spec.Ffdh.sievedParameterSearch, show Spec.Ffdh.sievedParameterCandidate p.c.bits p.c.gen
      (p.c.rand.drop used) = some (some prime, rest) from hc]
    simp only [Spec.Ffdh.ParameterSearchResult.consume, List.length_drop]

theorem searchTail_reject {p : SearchPublic} {used remaining : Nat} {rest : List Byte}
    (hr : 0 < remaining) (hc : searchCandidate p used = some (none, rest)) :
    searchTail p used remaining = searchTail p (used + (p.c.rand.length - used - rest.length))
      (remaining - 1) := by
  simpa only [searchTail, List.length_drop] using search_reject hr hc

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! # Total correctness of the complete native parameter-search loop -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search VG.Proof.Ffdh.X86_64.ParameterCandidate

def SearchInvariant (p : SearchPublic) (original : State) (expected : Spec.Ffdh.ParameterSearchResult)
    (n : Nat) (s : State) : Prop :=
  ∃ used remaining, n = remaining + 1 ∧ SearchLive p original used remaining s ∧
    expected = searchTail p used remaining

theorem search_iteration (v : RoundImpl) {p : SearchPublic} {original s : State}
    {expected : Spec.Ffdh.ParameterSearchResult} {n : Nat}
    (h : SearchInvariant p original expected n s) :
    WP isa (iteration (candidateCode v)) s fun t =>
      (eval .e t = some false ∧ SearchDone p original expected t) ∨
      (eval .e t = some true ∧ ∃ m < n, SearchInvariant p original expected m t) := by
  obtain ⟨used, remaining, hn, h, hexpected⟩ := h
  unfold iteration
  change WP isa (.seq _ (.seq _ _)) s _
  refine WP.seq (WP.mono (remaining_guard h) fun u ⟨hu, he⟩ => ?_)
  apply WP.seq
  refine WP.ite (decide (remaining = 0)) he ?_ ?_
  · intro hz
    have hz' := of_decide_eq_true hz
    have hresult : expected = .exhausted used := by rw [hexpected, hz', searchTail_zero]
    refine WP.mono (search_exhausted hu) fun t ht => ?_
    refine WP.mono (done_loop_guard ht) fun q ⟨hq, hdone⟩ => ?_
    exact Or.inl ⟨hq, by rw [hresult]; exact hdone⟩
  · intro hnz
    have hr : 0 < remaining := by omega_using [of_decide_eq_false hnz]
    refine WP.seq (WP.mono (search_candidate_run v hu) fun t ⟨ht, hp⟩ => ?_)
    refine WP.mono (search_classify ht hr hp) fun q hq => ?_
    cases hc : searchCandidate p used with
    | none =>
      simp only [SearchClassified, hc] at hq
      have hresult : expected = shortResult p used remaining := hexpected.trans (searchTail_short hr hc)
      refine WP.mono (done_loop_guard hq) fun z ⟨hz, hd⟩ => ?_
      exact Or.inl ⟨hz, by rw [hresult]; exact hd⟩
    | some pair =>
      obtain ⟨value, rest⟩ := pair
      cases value with
      | some prime =>
        simp only [SearchClassified, hc] at hq
        have hresult : expected = .accepted prime (used + (p.c.rand.length - used - rest.length)) :=
          hexpected.trans (searchTail_accept hr hc)
        refine WP.mono (done_loop_guard hq) fun z ⟨hz, hd⟩ => ?_
        exact Or.inl ⟨hz, by rw [hresult]; exact hd⟩
      | none =>
        simp only [SearchClassified, hc] at hq
        refine WP.mono (live_loop_guard hq.1 hq.2) fun z ⟨hz, hzlive⟩ => ?_
        refine Or.inr ⟨hz, remaining - 1 + 1, by omega_using [hn, hr], ?_⟩
        exact ⟨used + (p.c.rand.length - used - rest.length), remaining - 1,
          rfl, hzlive, hexpected.trans (searchTail_reject hr hc)⟩

theorem search_loop (v : RoundImpl) {p : SearchPublic} {original s : State}
    {expected : Spec.Ffdh.ParameterSearchResult} {n : Nat}
    (h : SearchInvariant p original expected n s) :
    WP isa (.loop (iteration (candidateCode v)) .e) s (SearchDone p original expected) := by
  exact WP.loop (M := isa) (body := iteration (candidateCode v)) (c := .e)
    (Q := SearchDone p original expected) (SearchInvariant p original expected)
    (fun _ _ h => search_iteration v h) n s h

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! ### `Ffdh.X86_64.Generation.SearchSafety`, which only this module used -/

section

/-! # The complete generation controller's instruction safety and stack bound -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64 VG.Impl.Bignum.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate
open VG.Impl.Ffdh.X86_64.Generation.Search

def searchCode (v : RoundImpl) : Prog isa := code (candidateCode v)

private theorem controller_all (p : Instr → Bool) (c : Prog isa)
    (hp : (code (.block [])).all p = true) (hc : c.all p = true) : (code c).all p = true := by
  unfold code iteration candidateRun at hp ⊢
  simp only [seqs, Code.all, List.all_nil, hc, Bool.and_true] at hp ⊢
  exact hp

private theorem controller_ctlC (c : Prog isa) (hp : ctlC (code (.block [])) = true) (hc : ctlC c = true) :
    ctlC (code c) = true := by
  unfold code iteration candidateRun at hp ⊢
  simp only [seqs, ctlC, hc, Bool.and_true] at hp ⊢
  exact hp

theorem searchCode_sp (v : RoundImpl) : (searchCode v).all (fun i => !isa.writesSp i) = true := by
  exact controller_all _ _ (by decide +kernel) (candidateCode_sp v)

/-- The search loads MXCSR only where the round restores it. -/
theorem searchCode_ctlC (v : RoundImpl) : ctlC (searchCode v) = true :=
  controller_ctlC _ (by decide +kernel) (candidateCode_ctlC v)

theorem searchCode_depth (v : RoundImpl) : (searchCode v).x86_64Depth ≤ 160 := by
  have he : exhausted.x86_64Depth = 0 := rfl
  have hc : classify.x86_64Depth = 0 := rfl
  unfold searchCode code iteration candidateRun
  simp only [seqs, Code.x86_64Depth, Instr.frameBytes, he, hc, Nat.zero_max, Nat.max_zero]
  exact Nat.add_le_add_right (candidateCode_depth v) 32

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! ### `Ffdh.X86_64.Generation.SearchCT`, which only this module used -/

section

/-! # Complete native parameter generation has the specified public-tape leakage -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/SearchCTStep.lean`, which only this module imported.
section

/-! # Public successor states for the native parameter-search timing proof -/

section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Impl.Ffdh.X86_64.Generation.Search

def searchContinues (p : SearchPoint) : Prop := p.remaining ≠ 0 ∧
  Proof.Ffdh.candidateStatus (searchCandidate p.inputs p.used) = 2

instance (p : SearchPoint) : Decidable (searchContinues p) := inferInstanceAs
  (Decidable (p.remaining ≠ 0 ∧ Proof.Ffdh.candidateStatus (searchCandidate p.inputs p.used) = 2))

def nextSearchPoint (p : SearchPoint) : SearchPoint :=
  { p with used := p.used + candidateUsed p.inputs p.used, remaining := p.remaining - 1 }

def SearchCTStep (p : SearchPoint) (s : State) : Prop :=
  if searchContinues p then eval .e s = some true ∧ SearchCTL (nextSearchPoint p) s
  else eval .e s = some false

theorem search_ct_step (v : RoundImpl) (p : SearchPoint) (s : State) (h : SearchCTL p s) :
    WP isa (iteration (candidateCode v)) s (SearchCTStep p) := by
  unfold iteration
  change WP isa (.seq _ (.seq _ _)) s _
  refine WP.seq (WP.mono (remaining_ready p s h) fun u hu => ?_)
  refine WP.seq (WP.mono (branch_ready v p u hu) fun t ht => ?_)
  by_cases hr : p.remaining = 0
  · simp only [SearchBranchResult, hr, ite_true] at ht
    obtain ⟨original, ht⟩ := ht
    refine WP.mono (done_loop_guard ht) fun q ⟨hq, _⟩ => ?_
    simp only [SearchCTStep, show ¬searchContinues p by simp [searchContinues, hr], ite_false]
    exact hq
  · simp only [SearchBranchResult, hr, ite_false] at ht
    obtain ⟨original, ht⟩ := ht
    cases hc : searchCandidate p.inputs p.used with
    | none =>
      simp only [SearchClassified, hc] at ht
      refine WP.mono (done_loop_guard ht) fun q ⟨hq, _⟩ => ?_
      simp only [SearchCTStep, show ¬searchContinues p by simp [searchContinues, hc, Proof.Ffdh.candidateStatus], ite_false]
      exact hq
    | some pair =>
      obtain ⟨value, rest⟩ := pair
      cases value with
      | some prime =>
        simp only [SearchClassified, hc] at ht
        refine WP.mono (done_loop_guard ht) fun q ⟨hq, _⟩ => ?_
        simp only [SearchCTStep, show ¬searchContinues p by simp [searchContinues, hc, Proof.Ffdh.candidateStatus], ite_false]
        exact hq
      | none =>
        simp only [SearchClassified, hc] at ht
        refine WP.mono (live_loop_guard ht.1 ht.2) fun q ⟨hq, hlive⟩ => ?_
        simp only [SearchCTStep, show searchContinues p by simp [searchContinues, hr, hc, Proof.Ffdh.candidateStatus], ite_true]
        exact ⟨hq, original, by simpa only [nextSearchPoint, candidateUsed, hc] using hlive⟩

end VG.Proof.Ffdh.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/SearchLoopCT.lean`, which only this module imported.
section

/-! # Repeated native candidate retries preserve the public timing relation -/

section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Impl.Ffdh.X86_64.Generation.Search

private def LoopPair (n : Nat) (s t : State) : Prop :=
  ∃ p, n = p.remaining + 1 ∧ SearchCTL p s ∧ SearchCTL p t

private theorem iteration_pair (v : RoundImpl) (n : Nat) :
    RelCT isa (LoopPair n) (iteration (candidateCode v)) fun s t =>
      eval .e s = eval .e t ∧ (eval .e s = some false → True) ∧
      (eval .e s = some true → ∃ m < n, LoopPair m s t) := by
  have hw (p : SearchPoint) (s : State) (h : n = p.remaining + 1 ∧ SearchCTL p s) :
      WP isa (iteration (candidateCode v)) s fun t => n = p.remaining + 1 ∧ SearchCTStep p t :=
    WP.mono (search_ct_step v p s h.2) fun _ ht => ⟨h.1, ht⟩
  have hc := two_post ((search_iteration_ct v).mono
    (fun _ _ ⟨p, h₁, h₂⟩ => ⟨p, h₁.2, h₂.2⟩) (fun _ _ h => h)) hw
  refine hc.mono (fun _ _ ⟨p, hn, h₁, h₂⟩ => ⟨p, ⟨hn, h₁⟩, hn, h₂⟩) ?_
  rintro s t ⟨p, ⟨hn, h₁⟩, _, h₂⟩
  by_cases hb : searchContinues p
  · simp only [SearchCTStep, hb, ite_true] at h₁ h₂
    refine ⟨h₁.1.trans h₂.1.symm, fun _ => trivial, fun _ => ?_⟩
    refine ⟨(nextSearchPoint p).remaining + 1, ?_, nextSearchPoint p, rfl, h₁.2, h₂.2⟩
    dsimp only [nextSearchPoint]
    omega_using [hn, hb.1]
  · simp only [SearchCTStep, hb, ite_false] at h₁ h₂
    refine ⟨h₁.trans h₂.symm, fun _ => trivial, fun ht => ?_⟩
    rw [h₁] at ht
    cases ht

theorem search_loop_ct (v : RoundImpl) :
    RelCT isa (Two SearchCTL) (.loop (iteration (candidateCode v)) .e) (fun _ _ => True) := by
  intro s t tr₁ tr₂ u₁ u₂ ⟨p, hs, ht⟩ he₁ he₂
  exact RelCT.loop (M := isa) (body := iteration (candidateCode v)) (c := .e)
    (Q := fun _ _ => True) LoopPair (iteration_pair v) (p.remaining + 1)
    _ _ _ _ _ _ ⟨p, rfl, hs, ht⟩ he₁ he₂

end VG.Proof.Ffdh.X86_64.Generation
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Impl.Ffdh.X86_64.Generation.Search

private def initialPoint (p : SearchPublic) : SearchPoint := ⟨p, 0, p.remaining⟩
private def finalPoint (p : SearchPublic) : SearchEndPoint := ⟨p, searchTail p 0 p.remaining⟩

private theorem entry_started (p : SearchPublic) (s : State) (h : SearchInput p s) :
    WP isa (.block entry) s (SearchCTL (initialPoint p)) :=
  WP.mono (search_start h) fun _ ht => ⟨s, ht⟩

private theorem loop_done (v : RoundImpl) (p : SearchPublic) (s : State) (h : SearchCTL (initialPoint p) s) :
    WP isa (.loop (iteration (candidateCode v)) .e) s (SearchCTDone (finalPoint p)) := by
  obtain ⟨original, h⟩ := h
  have hi : SearchInvariant p original (searchTail p 0 p.remaining) (p.remaining + 1) s :=
    ⟨0, p.remaining, rfl, h, rfl⟩
  exact WP.mono (search_loop v hi) fun _ ht => ⟨original, ht⟩

theorem search_code_ct (v : RoundImpl) :
    RelCT isa (Two SearchInput) (searchCode v) (fun _ _ => True) := by
  unfold searchCode code
  change RelCT isa _ (.seq _ (.seq _ _)) _
  exact RelCT.seq (two_post search_entry_ct entry_started)
    (RelCT.seq (two_post (two_map initialPoint (fun _ _ h => h) (search_loop_ct v)) (loop_done v))
      (two_map finalPoint (fun _ _ h => h) search_finish_ct))

private theorem search_public_descriptor {s t : State} (h : searchPub s t) : searchOfState s = searchOfState t := by
  obtain ⟨⟨hsp, hbytes, r0, r1, r2, r3, r4, r5, a0, a1, a2⟩, ac, hw⟩ := h
  have hrand := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hbytes
  have hc : candidateOfState s = candidateOfState t := by
    simp only [candidateOfState, r0, r1, r2, r3, r4, r5, a1, a2, hrand, hsp]
  change [word s.mem (stackArg s 3) 0, word s.mem (stackArg s 3) 8,
    word s.mem (stackArg s 3) 16, word s.mem (stackArg s 3) 24] =
      [word t.mem (stackArg t 3) 0, word t.mem (stackArg t 3) 8,
        word t.mem (stackArg t 3) 16, word t.mem (stackArg t 3) 24] at hw
  have hcounter : s.mem.readW (stackArg s 3) 64 = t.mem.readW (stackArg t 3) 64 := by
    simpa only [Bignum.word, off, BitVec.add_zero] using (List.cons.inj hw).1
  unfold searchOfState
  congr 1
  exact congrArg BitVec.toNat hcounter

theorem search_constantTime (v : RoundImpl) :
    ConstantTime isa searchContract.pre searchContract.pub (searchCode v) := by
  refine RelCT.constantTime ((search_code_ct v).mono ?_ (fun _ _ h => h))
  intro s t ⟨hs, ht, hp⟩
  exact ⟨searchOfState s, ⟨hs, rfl⟩, ht, (search_public_descriptor hp).symm⟩

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! ### `Ffdh.X86_64.Generation.SearchImplies`, which only this module used -/

section

/-! # Match the complete native controller to its shared callable contract -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Spec.Ffdh VG.Proof.Ffdh.X86_64.ParameterCandidate

theorem stackArgs_four (s : State) : List.map (stackArg s) (List.range 4) =
    [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3] := rfl

private theorem candidate_gpr (s : State) : (candidateState s).gpr = s.gpr := rfl

private theorem candidate_rd (s : State) : (candidateState s).rd =
    [inputRand s, ⟨stackArgAddr s 0, 24⟩] := rfl

private theorem candidate_wr (s : State) : (candidateState s).wr = inputBuffers s := rfl

private theorem candidate_arg (s : State) (j : Nat) : stackArg (candidateState s) j = stackArg s j := rfl

private theorem candidate_argAddr (s : State) (j : Nat) :
    stackArgAddr (candidateState s) j = stackArgAddr s j := rfl

theorem search_implies_pre (s : State) (h : (sievedParameterSearchContract abi 160).pre s) : searchContract.pre s := by
  sig_pre [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow,
    searchContract, searchPre, pcPre, inputRand, inputArgs, inputBuffers,
    inputControl, candidate_gpr, candidate_rd, candidate_wr, candidate_arg, candidate_argAddr, stackArgs_four, List.append_eq] at h
  sig_pre [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow,
    searchContract, searchPre, pcPre, inputRand, inputArgs, inputBuffers,
    inputControl, candidate_gpr, candidate_rd, candidate_wr, candidate_arg, candidate_argAddr, stackArgs_four, List.append_eq] at h
  sig_split h
  sig_reduce [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow,
    searchContract, searchPre, pcPre, inputRand, inputArgs, inputBuffers,
    inputControl, candidate_gpr, candidate_rd, candidate_wr, candidate_arg, candidate_argAddr, stackArgs_four, List.append_eq]
  simp only [candidate_arg, candidate_argAddr, List.forall_mem_cons,
    BitVec.ofNat_toNat, BitVec.setWidth_eq] at *
  have haSub : Region.Sub ⟨stackArgAddr s 0, 24⟩ ⟨stackArgAddr s 0, 32⟩ := by
    simpa only [BitVec.add_zero] using Offset.sub_base (stackArgAddr s 0)
      (d := 0) (n := 24) (k := 32) (by decide)
  have hbSub : Region.Sub (below (s.gpr .rsp) 128) (below (s.gpr .rsp) 160) :=
    Offset.below_mono _ (by decide) (by decide)
  sig_and_intros
  sig_close
  all_goals first
    | (intro x hx; cases hx)
    | exact True.intro
    | with_reducible assumption
    | with_reducible rfl
    | omega
    | with_reducible exact Region.Disjoint.symm ‹_›
    | exact Region.Disjoint.sub_left (r₁ := ⟨stackArgAddr s 0, 32⟩)
        (by first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›) haSub
    | exact Region.Disjoint.sub_right (r₂ := below (s.gpr .rsp) 160)
        (by first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›) hbSub
    | exact Region.Disjoint.sub_right (r₂ := ⟨stackArgAddr s 0, 32⟩)
        (by first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›) haSub
    | exact Region.Disjoint.sub_left (r₁ := below (s.gpr .rsp) 160)
        (by first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›) hbSub
    | exact (Region.Disjoint.sub_right (r₁ := ⟨stackArgAddr s 0, 32⟩)
        (r₂ := below (s.gpr .rsp) 160)
        (by first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›) hbSub).sub_left haSub
    | exact ((Region.Disjoint.sub_right (r₁ := ⟨stackArgAddr s 0, 32⟩)
        (r₂ := below (s.gpr .rsp) 160)
        (by first | with_reducible assumption | with_reducible exact Region.Disjoint.symm ‹_›) hbSub).sub_left haSub).symm

theorem search_implies_post : ∀ s t, (sievedParameterSearchContract abi 160).pre s →
    searchContract.post s t → (sievedParameterSearchContract abi 160).post s t := by
  sig_implies_post [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, searchContract,
    searchPost, searchResult, pcRand, stackArgs_four, List.append_eq, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem search_implies_pub (s t : State) (_hs : (sievedParameterSearchContract abi 160).pre s)
    (_ht : (sievedParameterSearchContract abi 160).pre t) (h : (sievedParameterSearchContract abi 160).pub s t) :
    searchContract.pub s t := by
  sig_pub [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackArgs_four,
    List.append_eq] at h
  simp only [List.getD_cons_succ, List.getD_cons_zero] at h
  obtain ⟨hsp, hleak, rdi, rsi, rdx, rcx, r8, r9, a0, a1, a2, ast⟩ := h
  have hlen : (List.map (fun x => x.toNat) (pcRand s)).length =
      (List.map (fun x => x.toNat) (pcRand t)).length := by
    simp only [pcRand, Spec.Rsa.bytesAt, List.length_map, List.length_range, a0]
  obtain ⟨hbytes, hwords⟩ := List.append_inj hleak hlen
  have hc := (List.map_inj_right (fun _ _ h => BitVec.toNat_inj.1 h)).1 hwords
  exact ⟨⟨hsp, hbytes, rdi, rsi, rdx, rcx, r8, r9, a0, a1, a2⟩, ast, hc⟩

private def searchSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 64 | .rdx => 0x2000 | .rcx => 512 | .r8 => 2 | .r9 => 0x3000
    | .rsp => 0x6000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem a := if a = 0x6011 then 0x80 else if a = 0x6018 then 0x20 else if a = 0x6019 then 0x04
    else if a = 0x6021 then 0x40 else if a = 0x4008 then 0x40 else if a = 0x4010 then 0x40
    else if a = 0x4012 then 0x20 else 0
  rd := [⟨0x3000, 0⟩, ⟨0x6008, 32⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 8⟩, ⟨0x8000, 1056 * 8⟩, ⟨0x4000, 128⟩]

theorem search_implies : searchContract.Implies (sievedParameterSearchContract abi 160) where
  pre := search_implies_pre
  post := search_implies_post
  pub := search_implies_pub
  sat := by
    sig_implies_sat [sievedParameterSearchContract, parameterSearchSig, abi, argRegs, stackBelow,
      searchContract, searchPre, stackArgs_four, List.append_eq, searchSat]
      [searchSat, stackArg, stackArgAddr, Mem.readW, Mem.read] using searchSat

end VG.Proof.Ffdh.X86_64.Generation

end

end

/-! # Verified complete native FFDH parameter generation for every arithmetic backend -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/SearchFinish.lean`, which only this module imported.
section

/-! # Returning a complete native search preserves its output and System V registers -/

section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Impl.Ffdh.X86_64.Generation.Search

def SearchReturned (p : SearchPublic) (result : Spec.Ffdh.ParameterSearchResult) (t : State) : Prop :=
  ((t.gpr .rax).setWidth 32).toNat = result.status ∧ SearchOutput p result t.mem ∧
    Spec.Rsa.wordsAt t.mem p.c.up 1 = [BitVec.ofNat 64 result.used] ∧
    Spec.Rsa.wordsAt t.mem p.control 4 =
      [BitVec.ofNat 64 result.remaining, BitVec.ofNat 64 p.c.k,
        BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits), BitVec.ofNat 64 (Proof.Ffdh.requested p.c.bits result)]

theorem search_finish {p : SearchPublic} {original s : State} {result : Spec.Ffdh.ParameterSearchResult}
    (h : SearchDone p original result s) :
    WP isa (.block finish) s fun t => SearchReturned p result t ∧
      (∀ reg ∈ calleeSaved, t.gpr reg = original.gpr reg) ∧ t.rd = original.rd ∧ t.wr = original.wr := by
  refine WP.mono (search_finish_values h) fun t ⟨ha, hr12, hm, k⟩ => ?_
  have hf : Frame [⟨p.c.up, 8⟩] s.mem t.mem := by
    rw [hm]
    exact Frame.writeW (Frame.refl _ _) (List.mem_singleton_self _) _ (Region.contains_self _ _)
  have ho : Spec.Rsa.bytesAt t.mem p.c.op p.c.k = Spec.Rsa.bytesAt s.mem p.c.op p.c.k := by
    simp only [Spec.Rsa.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact hf.bytes (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact h.input.output_used_disjoint)
      (Nat.le_of_lt h.input.length_lt) (List.mem_range.mp hi)
  have hc (j : Nat) (hj : j < 4) : word t.mem p.control (8 * j) = word s.mem p.control (8 * j) :=
    hf.readW (r := ⟨p.control, 128⟩)
      (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hj]))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact h.input.control_used_disjoint) (by decide)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, k.2.1.trans h.rd, k.2.2.trans h.wr⟩
  · rw [ha]
    cases result <;> rfl
  · change Spec.Rsa.bytesAt t.mem p.c.op p.c.k = _
    rw [ho]
    exact h.output
  · change [word t.mem p.c.up 0] = [_]
    rw [hm]
    congr 1
    simpa only [Bignum.word, off, BitVec.add_zero] using
      Mem.readW_writeW_self64 s.mem p.c.up (BitVec.ofNat 64 result.used)
  · have he : Spec.Rsa.wordsAt t.mem p.control 4 = Spec.Rsa.wordsAt s.mem p.control 4 := by
      change [word t.mem p.control 0, word t.mem p.control 8, word t.mem p.control 16, word t.mem p.control 24] = _
      rw [hc 0 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide)]
      rfl
    exact he.trans h.policy
  · intro reg hreg
    by_cases he : reg = .r12
    · subst he; exact hr12
    · exact (k.gpr (by cases reg <;> simp_all [calleeSaved])).trans (h.saved reg hreg he)

end VG.Proof.Ffdh.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/SearchCorrect.lean`, which only this module imported.
section

/-! # Complete native parameter-generation correctness -/

section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.X86_64.ParameterCandidate VG.Proof.Ffdh.Generation
open VG.Impl.Ffdh.X86_64.Generation.Search

theorem initial_search_result {p : SearchPublic} {s : State} (h : SearchInput p s) :
    searchResult s = searchTail p 0 p.remaining := by
  cases h.2
  simp only [searchResult, searchTail, searchOfState, SearchPublic.c, candidateOfState,
    List.drop_zero, consume_zero]

theorem returned_post {p : SearchPublic} {s t : State} (h : SearchInput p s)
    (hr : SearchReturned p (searchResult s) t) : searchPost s t := by
  have hreq : (searchResult s).Requests (Spec.Ffdh.parameterEntropy (s.gpr .rcx).toNat)
      (Proof.Ffdh.requested (s.gpr .rcx).toNat (searchResult s)) :=
    SievedGeneration.search_requests _ _ _ _
  cases h.2
  simp only [SearchReturned, SearchOutput, searchPost, searchOfState, SearchPublic.c,
    candidateOfState, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hr ⊢
  cases he : searchResult s <;> simp only [he] at hr hreq ⊢ <;>
    exact ⟨hr.1, hr.2.1, hr.2.2.1, _, hr.2.2.2, hreq⟩

theorem search_correct_ok (v : RoundImpl) {s : State} (h : searchPre s) :
    WP isa (code (candidateCode v)) s fun t => searchPost s t ∧
      (∀ reg ∈ calleeSaved, t.gpr reg = s.gpr reg) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  let p := searchOfState s
  have hp : SearchInput p s := ⟨h, rfl⟩
  unfold code
  change WP isa (.seq _ (.seq _ _)) s _
  refine WP.seq (WP.mono (search_start hp) fun u hu => ?_)
  have hinv : SearchInvariant p s (searchResult s) (p.remaining + 1) u :=
    ⟨0, p.remaining, rfl, hu, initial_search_result hp⟩
  refine WP.seq (WP.mono (search_loop v hinv) fun t ht => ?_)
  refine WP.mono (search_finish ht) fun q ⟨hr, hg, hrd, hwr⟩ => ?_
  exact ⟨returned_post hp hr, hg, hrd, hwr⟩

end VG.Proof.Ffdh.X86_64.Generation
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/Generation/SearchAbi.lean`, which only this module imported.
section

/-! # Complete native parameter generation preserves the System V ABI -/

section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

private theorem search_return_address (v : RoundImpl) {s t : State} {tr : List Leak}
    (h : searchPre s) (he : Exec isa (searchCode v) s tr t) :
    t.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  have hrc : (⟨s.gpr .rsp, 8⟩ : Region).Disjoint (inputControl s) :=
    (h.2.2.2.2.2.1 _ (by simp)).symm
  have hwr := h.2.2.2.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hro, hru, _, hrs, _⟩ := h.1
  have hd := searchCode_depth v
  have hf := Exec.stackFrame (SpSafe.of_all (searchCode_sp v)) he (by omega_using [hd])
  refine hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · rw [hwr] at hr
    simp only [inputBuffers, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    exacts [hro, hru, hrs, hrc]
  · obtain rfl := List.mem_singleton.mp hr
    exact Offset.base_disjoint_below _ (by omega_using [hd])

theorem search_correct (v : RoundImpl) (s : State) (h : searchContract.pre s) :
    ∃ tr t, Exec isa (searchCode v) s tr t ∧ abiPreserved s t ∧ searchContract.post s t := by
  obtain ⟨tr, t, he, hp, hg, _, _⟩ := search_correct_ok v h
  exact ⟨tr, t, he, abiPreserved_of_ctl (ctlOk_of_ctlC (searchCode_ctlC v)) he
    ⟨hg, search_return_address v h he⟩, hp⟩

end VG.Proof.Ffdh.X86_64.Generation
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Generation

open VG VG.X86_64 VG.Proof.MillerRabin.X86_64

theorem search_verified (v : RoundImpl) : Verified target (searchCode v)
    (Spec.Ffdh.sievedParameterSearchContract abi 160) := by
  exact Verified.of_correct (search_correct v) (search_constantTime v) search_implies

end VG.Proof.Ffdh.X86_64.Generation
