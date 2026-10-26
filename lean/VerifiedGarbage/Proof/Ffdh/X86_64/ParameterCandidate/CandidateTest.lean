module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PolicyResult

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TestQ
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeOriginal
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Consume
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseSetup
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LoadOutput
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CheckGenerator
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CheckPrime
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LeavePhase
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Algebra.Group.Nat.Defs

/-! # FFDH parameter generation on x86-64: the complete candidate test -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64 (seqs)
open VG.Impl.Rsa.X86_64.Crt
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64

def candidateTail (p : CandidateP) (r : List Byte) : Option (Bool × List Byte) :=
  if Spec.Ffdh.generationShape p.bits p.gen p.P && Spec.Ffdh.primeShape p.P then qPolicy p r
  else some (false, r)

def CandidateTestPost (p : CandidateP) (s t : State) : Prop :=
  ∃ n, n ≤ (p.rand.drop p.k).length ∧ CandidateTape p (p.k + n) t ∧ t.gpr .rdi = p.B ∧
    TapeOutcome p p.k n (candidateTail p (p.rand.drop p.k)) t.mem ∧
    (word t.mem p.B (8 * oStatus) = 1 → Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem p.op p.k) = p.P) ∧
    CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t

theorem testCandidate_ok (M : Mont) (R : R2Impl M) (K : Kernel)
    {p : CandidateP} {s : State} (h : CandidateTape p 0 s)
    (hdi : s.gpr .rdi = p.B) (havail : p.k ≤ p.rand.length) :
    WP isa (testCandidate M.mm R.code K.run) s (CandidateTestPost p s) := by
  unfold testCandidate
  simp only [seqs]
  refine WP.seq (WP.mono (shapeOriginal_ok h hdi havail) fun s₁ ⟨h₁, hd₁, hv₁, hs₁, hf₁, k₁, _⟩ => ?_)
  refine WP.seq (WP.mono (consumeCandidate_ok h₁ hd₁ havail) fun s₂ ⟨h₂, hs₂, hf₂, k₂, ho₂⟩ => ?_)
  have hd₂ : s₂.gpr .rdi = p.B := (k₂.gpr (by decide)).trans hd₁
  unfold candidateFilter
  simp only [seqs]
  refine WP.seq (WP.mono (phaseSetup_state_ok h₂ hd₂ false)
    fun s₃ ⟨mi, h₃, hg₃, hp₃, hs₃, hf₃, k₃, ho₃⟩ => ?_)
  refine WP.seq (WP.mono (loadOutput_ok h₃ hg₃ hp₃ (by rw [ho₃, ho₂]; exact hv₁))
    fun s₄ ⟨h₄, hg₄, hp₄, hn₄, hs₄, hf₄, k₄, ho₄⟩ => ?_)
  have hs := ((hs₁.trans hs₂).trans hs₃).trans hs₄
  have hf := ((hf₁.trans hf₂).trans hf₃).trans hf₄
  have kk : Keep (.rdi :: mmRegs) s s₄ := (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)
  have hv₄ : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s₄.mem p.op p.k) = p.P := by rw [ho₄, ho₃, ho₂]; exact hv₁
  refine WP.seq (WP.mono (generatorCheck_state_ok h₄ hg₄ hp₄ hn₄)
    fun s₅ ⟨h₅, hg₅, hp₅, hn₅, hz₅, hm₅, k₅⟩ => ?_)
  obtain ⟨_, hs₅, hf₅⟩ := h₄.same_mem hm₅ k₅ (by decide)
  have hs' := hs.trans hs₅
  have hf' := hf.trans hf₅
  have kk' : Keep (.rdi :: mmRegs) s s₅ := (kk.trans k₅).mono (by decide)
  refine WP.ite (Spec.Ffdh.generationShape p.bits p.gen p.P) (by simp [eval, hz₅]) ?_ ?_
  · intro hgen
    refine WP.seq (WP.mono (primeCheck_state_ok h₅ hg₅ hp₅ hn₅)
      fun s₆ ⟨h₆, hg₆, hp₆, _, hz₆, hs₆, hf₆, k₆, ho₆⟩ => ?_)
    have hs'' := hs'.trans hs₆
    have hf'' := hf'.trans hf₆
    have kk'' : Keep (.rdi :: mmRegs) s s₆ := (kk'.trans k₆).mono (by decide)
    refine WP.ite (Spec.Ffdh.primeShape p.P) (by simpa [eval, CandidateP.phaseValue] using hz₆) ?_ ?_
    · intro hprime
      refine WP.seq (WP.mono (leavePhase_ok h₆ hg₆.rdi hp₆.link)
        fun s₇ ⟨h₇, hd₇, hm₇, hs₇, hf₇, k₇⟩ => ?_)
      refine WP.mono (testQ_ok M R K h₇ hd₇ havail (by rw [hm₇, ho₆, hm₅]; exact hv₄))
        fun t ⟨n, hn, ht, hdt, hr, hv, hst, hft, kt⟩ => ?_
      exact ⟨n, hn, ht, hdt, by simpa only [candidateTail, hgen, hprime, Bool.and_self, ite_true] using hr,
        hv, (hs''.trans hs₇).trans hst, (hf''.trans hf₇).trans hft,
        ((kk''.trans k₇).trans kt).mono (by decide)⟩
    · intro hprime
      refine WP.mono (innerStatus_ok h₆ hg₆.rdi hp₆.link (n := 2) (by decide))
        fun t ⟨ht, hdt, hstatus, hst, hft, kt⟩ => ?_
      refine ⟨0, Nat.zero_le _, by simpa only [Nat.add_zero] using ht, hdt, ?_,
        fun he => by rw [hstatus] at he; contradiction, hs''.trans hst, hf''.trans hft,
        (kk''.trans kt).mono (by decide)⟩
      simp [candidateTail, hprime, TapeOutcome, hstatus]
  · intro hgen
    refine WP.mono (innerStatus_ok h₅ hg₅.rdi hp₅.link (n := 2) (by decide))
      fun t ⟨ht, hdt, hstatus, hst, hft, kt⟩ => ?_
    refine ⟨0, Nat.zero_le _, by simpa only [Nat.add_zero] using ht, hdt, ?_,
      fun he => by rw [hstatus] at he; contradiction, hs'.trans hst, hf'.trans hft,
      (kk'.trans kt).mono (by decide)⟩
    simp [candidateTail, hgen, TapeOutcome, hstatus]

end VG.Proof.Ffdh.X86_64.ParameterCandidate
