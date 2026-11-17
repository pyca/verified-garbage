module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCTData
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchClassify
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Safety
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchShort
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchGuards
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCandidatePost
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRestore
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Depth
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.AbiCorrect
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCallLayout
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.Inline
import Mathlib.Algebra.Group.Nat.Defs

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
  refine ⟨?_, htw.trans k.2.2, ?_⟩
  · exact htsp.trans (k.gpr (by decide))
  · have hframe := (arguments_frame h hm).trans (call_frame h (by
      simpa only [hsp, h.rsp] using hf))
    have hg : ∀ r ∈ calleeSaved, (freed 32 t).gpr r = s.gpr r := by
      intro r hr
      by_cases he : r = .rsp
      · subst he
        rw [freed_rsp, htsp, hsp]
        exact BitVec.sub_add_cancel _ _
      · rw [freed_reg _ _ _ he, habi.1 r hr, k.gpr (by cases r <;> simp_all [calleeSaved]),
          allocated_reg _ _ _ he]
    have hlive := h.restore (show (freed 32 t).rd = s.rd from htr.trans k.2.1)
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
    exact ⟨hlive, hout.freed⟩

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
