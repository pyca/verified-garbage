module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCandidatePost
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Safety
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchRestore
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Depth
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.AbiCorrect
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchCallLayout
import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.Inline

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
    (SpSafe.of_all (candidateCode_sp v)) (candidateCode_depth v) (candidateCode_mx v)
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
