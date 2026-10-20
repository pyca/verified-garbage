module

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.TestP
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PolicyResult
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.HalveOutput
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseSetup
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LoadOutput
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CheckPrime
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LeavePhase
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ModulusPolicy

/-! # FFDH parameter generation on x86-64: q followed by p -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64 (seqs)
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64

def TestQPost (p : CandidateP) (used : Nat) (s t : State) : Prop :=
  ∃ consumed, consumed ≤ (p.rand.drop used).length ∧ CandidateTape p (used + consumed) t ∧
    t.gpr .rdi = p.B ∧ TapeOutcome p used consumed (qPolicy p (p.rand.drop used)) t.mem ∧
    (word t.mem p.B (8 * oStatus) = 1 → Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem p.op p.k) = p.P) ∧
    CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t

theorem testQ_ok (M : Mont) (R : R2Impl M) (K : Kernel)
    {p : CandidateP} {used : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B) (havail : p.k ≤ p.rand.length)
    (hv : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem p.op p.k) = p.P) :
    WP isa (testQ M.mm R.code K.run) s (TestQPost p used s) := by
  unfold testQ
  simp only [seqs]
  refine WP.seq (WP.mono (halveOutput_ok h hdi hv) fun s₁ ⟨h₁, hd₁, hv₁, hs₁, hf₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (phaseSetup_state_ok h₁ hd₁ true)
    fun s₂ ⟨mi, h₂, hg₂, hp₂, hs₂, hf₂, k₂, ho₂⟩ => ?_)
  refine WP.seq (WP.mono (loadOutput_ok h₂ hg₂ hp₂ (by rw [ho₂]; exact hv₁))
    fun s₃ ⟨h₃, hg₃, hp₃, hn₃, hs₃, hf₃, k₃, _⟩ => ?_)
  refine WP.seq (WP.mono (primeCheck_state_ok h₃ hg₃ hp₃ hn₃)
    fun s₄ ⟨h₄, hg₄, hp₄, hn₄, hz₄, hs₄, hf₄, k₄, _⟩ => ?_)
  have hs := ((hs₁.trans hs₂).trans hs₃).trans hs₄
  have hf := ((hf₁.trans hf₂).trans hf₃).trans hf₄
  have kk : Keep (.rdi :: mmRegs) s s₄ := (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)
  refine WP.ite (Spec.Ffdh.primeShape p.Q) (by simpa [eval, CandidateP.phaseValue] using hz₄) ?_ ?_
  · intro hshape
    have hodd : p.phaseValue true % 2 = 1 := by
      change p.Q % 2 = 1
      have hh := hshape
      unfold Spec.Ffdh.primeShape at hh
      exact beq_iff_eq.mp ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hh).1).2
    refine WP.seq (WP.mono (modulusPolicy_ok M R K h₄ hg₄ hp₄ hn₄ hodd)
      fun s₅ ⟨n, hn, h₅, hd₅, hl₅, hr₅, hs₅, hf₅, k₅⟩ => ?_)
    refine WP.seq (WP.mono (leaveStatus_ok h₅ hd₅ hl₅)
      fun s₆ ⟨h₆, hd₆, hz₆, hm₆, hs₆, hf₆, k₆⟩ => ?_)
    have hs' := (hs.trans hs₅).trans hs₆
    have hf' := (hf.trans hf₅).trans hf₆
    have kk' : Keep (.rdi :: mmRegs) s s₆ := ((kk.trans k₅).trans k₆).mono (by decide)
    have hr₆ : PhaseOutcome p used n true s₆.mem := hr₅.congr (by rw [hm₆])
    refine WP.ite (word s₅.mem p.B (8 * oStatus) == 1) (by simp [eval, hz₆]) ?_ ?_
    · intro hyes
      have hy : word s₆.mem p.B (8 * oStatus) = 1 := by rw [hm₆]; exact beq_iff_eq.mp hyes
      refine WP.mono (testP_ok M R K h₆ hd₆ havail)
        fun t ⟨k, hk, ht, hdt, hrt, hvt, hst, hft, kt⟩ => ?_
      refine ⟨n + k, ?_, ?_, hdt, qPolicy_pass hshape hr₆ hy hrt, hvt,
        hs'.trans hst, hf'.trans hft, (kk'.trans kt).mono (by decide)⟩
      · rw [List.length_drop] at hk hn ⊢; omega_using [hk, hn, h.bound]
      · simpa only [Nat.add_assoc] using ht
    · intro hno
      have hnot : word s₆.mem p.B (8 * oStatus) ≠ 1 := by
        intro he; rw [hm₆] at he; simp [he] at hno
      exact WP.block_nil ⟨n, hn, h₆, hd₆, qPolicy_stop hshape hr₆ hnot,
        fun he => False.elim (hnot he), hs', hf', kk'⟩
  · intro hshape
    refine WP.mono (innerStatus_ok h₄ hg₄.rdi hp₄.link (n := 2) (by decide))
      fun t ⟨ht, hdt, hst, hsave, hframe, kt⟩ => ?_
    exact ⟨0, Nat.zero_le _, by simpa only [Nat.add_zero] using ht, hdt,
      qPolicy_reject hshape hst, fun he => by rw [hst] at he; contradiction,
      hs.trans hsave, hf.trans hframe, (kk.trans kt).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
