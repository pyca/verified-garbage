module

public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.AttemptRun
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Attempt
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.CallFacts
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.CallEntry
import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Live
import VerifiedGarbage.Proof.Framework.X86_64.CallFrame

/-! # The attempt, from the controller's loop state -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.KeyGeneration

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64 VG.Proof.Ffdh.KeyGeneration
open VG.Proof.Ffdh.X86_64.Generation (writeController allocated freed allocated_rsp allocated_reg
  freed_rsp freed_reg frame_alloc)
open VG.Proof.Ffdh.X86_64.GenerateKey (gkPost generateCode generateCode_sp gkDom gkRand gkA gkS)
open VG.Impl.Ffdh.X86_64.KeyGeneration.Search

theorem KeyInput.domain_valid {p : KeyPublic} {s : State} (h : KeyInput p s) :
    Spec.Ffdh.domainValid p.len p.dom := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hv, -, -, -⟩ := h.1
  rw [← h.2]; exact hv

/-- The attempt's view of the domain and the tape, at its entry. -/
theorem call_inputs {p : KeyPublic} {original s u : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen)
    (hf : CallFacts p used)
    (hm : u.mem = writeController s.mem (s.gpr .rsp - 40) (callValues p used))
    (hu : u.gpr .rsp = p.sp - 40) (ha : KeyArgs p u) :
    gkDom (callState p used u) = p.dom ∧
      gkRand (callState p used u) = ((keyRand original).drop used).take p.len ∧
      (stackArg (callState p used u) 0).toNat = p.len := by
  have hfr := call_mem_frame h hm hu
  obtain ⟨h0, h1, h2, -, -⟩ := call_args hu h.rsp hm
  have hlen : (BitVec.ofNat 64 p.len).toNat = p.len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.len64]
  have hdl : (BitVec.ofNat 64 p.dlen).toNat = p.dlen := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf.dlen64]
  refine ⟨?_, ?_, by rw [h0, hlen]⟩
  · simp only [gkDom, call_gpr (by decide : Reg.r8 ≠ .rsp), call_gpr (by decide : Reg.r9 ≠ .rsp),
      ha.2.2.2.2.1, ha.2.2.2.2.2, hdl]
    exact (h.input.domain_frame hfr).trans h.domain
  · simp only [gkRand, h1, h2, hlen]
    have hr := (h.input.random_frame hfr).trans h.random
    rw [← VG.Proof.Dsa.bytesAt_slice _ _ hroom, ← hr]

theorem key_attempt_run (v : RoundImpl) {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) (hroom : used + p.len ≤ p.randLen) :
    WP isa (attemptRun (attemptCall v)) s fun t =>
      KeyLive p original used keys scalars t ∧ AttemptPost p (keyRand original) used t := by
  have hf := h.callFacts hroom
  have hroom' : 40 ≤ (s.gpr .rsp).toNat := by rw [h.rsp]; have := hf.room; omega
  unfold attemptRun
  apply frame_alloc (by decide) (by decide) (by decide) hroom'
  refine WP.seq (WP.mono (key_arguments_ok h) fun u ⟨ha, hm, k⟩ => ?_)
  have hu : u.gpr .rsp = p.sp - 40 := by
    rw [k.gpr (by decide), allocated_rsp, h.rsp]; rfl
  have hpre := call_attempt_pre hf h.rsp hu ha hm
  have hd := generateCode_depth v
  refine WP.callF (k := attemptContract) (attempt_correct v) (SpSafe.of_all (generateCode_sp v))
    (by omega) hpre (call_covers_reads h hroom k.2.1 k.2.2) (call_covers_writes h k.2.2) ?_
  intro t hrd hwr hcs hfr ⟨s₂, hm₂, hg₂, hpost⟩ _
  have htsp : t.gpr .rsp = u.gpr .rsp := hcs .rsp (by decide)
  refine ⟨htsp.trans (k.gpr (by decide)), hwr.trans k.2.2, ?_, ?_⟩
  · -- The loop state, after the frame.
    apply h.restore (show (freed 40 t).rd = s.rd from hrd.trans k.2.1)
      (show (freed 40 t).wr = s.wr from by change t.wr.tail = s.wr; rw [hwr, k.2.2]; rfl)
    · intro r hr
      by_cases he : r = .rsp
      · subst he
        rw [freed_rsp, htsp, k.gpr (by decide), allocated_rsp]
        exact BitVec.sub_add_cancel _ _
      · rw [freed_reg _ _ _ he, hcs r hr, k.gpr (by cases r <;> simp_all [calleeSaved]),
          allocated_reg _ _ _ he]
    · exact attempt_frame h hm hu hd hfr
  · -- The attempt's status and outputs.
    obtain ⟨hdom, hrand, h0⟩ := call_inputs h hroom hf hm hu ha
    have hp := hpost
    simp only [attemptContract, gkPost, gkA, gkS, hdom, hrand, h0] at hp
    obtain ⟨hst, hout⟩ := hp h.input.domain_valid
    have hrax : (freed 40 t).gpr .rax = s₂.gpr .rax := by
      rw [freed_reg _ _ _ (by decide), hg₂ .rax (by decide)]
    have hmem : (freed 40 t).mem = s₂.mem := hm₂.symm
    simp only [call_gpr (by decide : Reg.rdi ≠ .rsp), call_gpr (by decide : Reg.rdx ≠ .rsp),
      ha.1, ha.2.2.1] at hout
    unfold AttemptPost
    rw [hrax, hmem]
    exact ⟨hst, hout⟩

end VG.Proof.Ffdh.X86_64.KeyGeneration
