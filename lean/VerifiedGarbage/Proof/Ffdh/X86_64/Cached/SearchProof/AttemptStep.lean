module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.AttemptRun
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Attempt
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.CallFacts
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.CallEntry
import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Live
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame

/-! # The attempt, from the controller's loop state -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.Cached.SearchProof

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Proof.Ffdh.GenerationSearch
open VG.Proof.Ffdh.X86_64.Generation (writeController allocated freed allocated_rsp allocated_reg
  freed_rsp freed_reg frame_alloc)
open VG.Proof.Ffdh.X86_64.Cached (cgPost attemptCode attemptCode_sp cgDom cgRand cgA cgS)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search hiding attemptRun attemptOrRequest iteration code
open VG.Impl.Ffdh.X86_64.Cached.Search

theorem KeyInput.domain_valid {p : KeyPublic} {s : State} (h : KeyInput p s) :
    Spec.Ffdh.domainValid p.len p.dom := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hv, -, -, -⟩ := h.1
  rw [← h.2]; exact hv

theorem KeyInput.context_pre {p : KeyPublic} {s : State} (h : KeyInput p s) :
    p.ctxLen = Spec.Ffdh.generationPrecomputedWords p.len ∧
      Spec.Ffdh.generationPrecompute p.len p.dom = some (Spec.Rsa.wordsAt s.mem p.ctx p.ctxLen) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcl, hpc⟩ := h.1
  rw [← h.2]; exact ⟨hcl, hpc⟩

/-- The attempt's view of the domain and the tape, at its entry. -/
theorem call_inputs {p : KeyPublic} {original s u : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen)
    (hf : CallFacts p used)
    (hm : u.mem = writeController s.mem (s.gpr .rsp - 56) (callValues p used))
    (hu : u.gpr .rsp = p.sp - 56) (ha : KeyArgs p u) :
    cgDom (callState p used u) = p.dom ∧
      cgRand (callState p used u) = ((keyRand original).drop used).take p.len ∧
      (stackArg (callState p used u) 0).toNat = p.len ∧
      Spec.Rsa.wordsAt (callState p used u).mem p.ctx p.ctxLen = Spec.Rsa.wordsAt original.mem p.ctx p.ctxLen := by
  have hfr := call_mem_frame h hm hu
  obtain ⟨h0, h1, h2, -, -⟩ := call_args hu h.rsp hm
  have hlen : (BitVec.ofNat 64 p.len).toNat = p.len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.len64]
  have hdl : (BitVec.ofNat 64 p.dlen).toNat = p.dlen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.dlen64]
  refine ⟨?_, ?_, by rw [h0, hlen], (h.input.context_frame hfr).trans h.context⟩
  · simp only [cgDom, call_gpr (by decide : Reg.r8 ≠ .rsp), call_gpr (by decide : Reg.r9 ≠ .rsp),
      ha.2.2.2.2.1, ha.2.2.2.2.2, hdl]
    exact (h.input.domain_frame hfr).trans h.domain
  · simp only [cgRand, h1, h2, hlen]
    have hr := (h.input.random_frame hfr).trans h.random
    rw [← VG.Proof.Dsa.bytesAt_slice _ _ hroom, ← hr]

/-- The attempt's precondition at its entry. -/
theorem call_pre {p : KeyPublic} {original s u : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen)
    (hf : CallFacts p used)
    (hm : u.mem = writeController s.mem (s.gpr .rsp - 56) (callValues p used))
    (hu : u.gpr .rsp = p.sp - 56) (ha : KeyArgs p u) :
    attemptContract.pre (callState p used u) := by
  obtain ⟨hdom, -, -, hctx⟩ := call_inputs h hroom hf hm hu ha
  have hcp := h.input.context_pre
  have hdom' : Spec.Rsa.bytesAt (callState p used u).mem p.dp p.dlen = p.dom := by
    have := hdom
    simp only [cgDom, call_gpr (by decide : Reg.r8 ≠ .rsp), call_gpr (by decide : Reg.r9 ≠ .rsp),
      ha.2.2.2.2.1, ha.2.2.2.2.2] at this
    rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.dlen64] at this
  exact call_attempt_pre hf h.rsp hu ha hm hdom' h.input.domain_valid hcp.1 (by rw [hctx]; exact hcp.2)

theorem key_attempt_run (v : RoundImpl) {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen) :
    WP isa (attemptRun (attemptCall v)) s fun t =>
      KeyLive p original used keys scalars t ∧ AttemptPost p (keyRand original) used t := by
  have hf := h.callFacts hroom
  have hroom' : 56 ≤ (s.gpr .rsp).toNat := by rw [h.rsp]; have := hf.room; omega
  unfold attemptRun
  apply frame_alloc (by decide) (by decide) (by decide) hroom'
  refine WP.seq (WP.mono (key_arguments_ok h) fun u ⟨ha, hm, k⟩ => ?_)
  have hu : u.gpr .rsp = p.sp - 56 := by
    rw [k.gpr (by decide), allocated_rsp, h.rsp]; rfl
  obtain ⟨hdom, hrand, h0, -⟩ := call_inputs h hroom hf hm hu ha
  have hpre := call_pre h hroom hf hm hu ha
  have hd := attemptCode_depth v
  refine WP.callF (k := attemptContract) (attempt_correct v) (SpSafe.of_all (attemptCode_sp v))
    (by omega) hpre (call_covers_reads h hroom k.2.1 k.2.2) (call_covers_writes h k.2.2) ?_
  intro t hrd hwr hcs hfr ⟨s₂, hm₂, hg₂, hpost⟩ _
  have htsp : t.gpr .rsp = u.gpr .rsp := hcs .rsp (by decide)
  refine ⟨htsp.trans (k.gpr (by decide)), hwr.trans k.2.2, ?_, ?_⟩
  · -- The loop state, after the frame.
    apply h.restore (show (freed 56 t).rd = s.rd from hrd.trans k.2.1)
      (show (freed 56 t).wr = s.wr from by change t.wr.tail = s.wr; rw [hwr, k.2.2]; rfl)
    · intro r hr
      by_cases he : r = .rsp
      · subst he
        rw [freed_rsp, htsp, k.gpr (by decide), allocated_rsp]
        exact BitVec.sub_add_cancel _ _
      · rw [freed_reg _ _ _ he, hcs r hr, k.gpr (by
        simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
          allocated_reg _ _ _ he]
    · exact attempt_frame h hm hu hd hfr
  · -- The attempt's status and outputs.
    have hp := hpost
    simp only [attemptContract, cgPost, cgA, cgS, hdom, hrand, h0] at hp
    obtain ⟨hst, hout⟩ := hp
    have hrax : (freed 56 t).gpr .rax = s₂.gpr .rax := by
      rw [freed_reg _ _ _ (by decide), hg₂ .rax (by decide)]
    have hmem : (freed 56 t).mem = s₂.mem := hm₂.symm
    simp only [call_gpr (by decide : Reg.rdi ≠ .rsp), call_gpr (by decide : Reg.rdx ≠ .rsp),
      ha.1, ha.2.2.1] at hout
    unfold AttemptPost
    rw [hrax, hmem]
    exact ⟨hst, hout⟩

end VG.Proof.Ffdh.X86_64.Cached.SearchProof
