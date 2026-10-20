module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCTData
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Safety
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.AbiCorrect
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Depth
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCallLayout
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCTData
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Safety
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.AbiCorrect
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Depth
meta import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCallLayout
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

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
    (SpSafe.of_all (candidateCode_sp v)) (candidateCode_depth v) (candidateCode_mx v)
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
