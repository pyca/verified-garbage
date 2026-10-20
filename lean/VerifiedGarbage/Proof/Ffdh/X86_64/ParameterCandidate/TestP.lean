module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseRounds

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ModulusPolicy
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeOriginal
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseSetup
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LoadOutput
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LeavePhase
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape

/-! # FFDH parameter generation on x86-64: the p primality phase -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64 (seqs)
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64

def TestPPost (p : CandidateP) (used : Nat) (s t : State) : Prop :=
  ∃ consumed, consumed ≤ (p.rand.drop used).length ∧ CandidateTape p (used + consumed) t ∧
    t.gpr .rdi = p.B ∧ PhaseOutcome p used consumed false t.mem ∧
    (word t.mem p.B (8 * oStatus) = 1 → Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem p.op p.k) = p.P) ∧
    CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t

theorem testP_ok (M : Mont) (R : R2Impl M) (K : Kernel)
    {p : CandidateP} {used : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B) (havail : p.k ≤ p.rand.length) :
    WP isa (testP M.mm R.code K.run) s (TestPPost p used s) := by
  unfold testP
  simp only [seqs]
  refine WP.seq (WP.mono (shapeOriginal_ok h hdi havail) fun s₁ ⟨h₁, hd₁, hv₁, hs₁, hf₁, k₁, _⟩ => ?_)
  refine WP.seq (WP.mono (phaseSetup_state_ok h₁ hd₁ false)
    fun s₂ ⟨mi, h₂, hg₂, hp₂, hs₂, hf₂, k₂, ho₂⟩ => ?_)
  refine WP.seq (WP.mono (loadOutput_ok h₂ hg₂ hp₂ (by rw [ho₂]; exact hv₁))
    fun s₃ ⟨h₃, hg₃, hp₃, hn₃, hs₃, hf₃, k₃, _⟩ => ?_)
  have hodd : p.phaseValue false % 2 = 1 :=
    (VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) (by omega_using [h.base.bits1]) _).1
  refine WP.seq (WP.mono (modulusPolicy_ok M R K h₃ hg₃ hp₃ hn₃ hodd)
    fun s₄ ⟨n, hn, h₄, hd₄, hl₄, hr₄, hs₄, hf₄, k₄⟩ => ?_)
  refine WP.seq (WP.mono (leaveStatus_ok h₄ hd₄ hl₄)
    fun s₅ ⟨h₅, hd₅, hz₅, hm₅, hs₅, hf₅, k₅⟩ => ?_)
  have hs := (((hs₁.trans hs₂).trans hs₃).trans hs₄).trans hs₅
  have hf := (((hf₁.trans hf₂).trans hf₃).trans hf₄).trans hf₅
  have kk : Keep (.rdi :: mmRegs) s s₅ := ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)
  have hr₅ : PhaseOutcome p used n false s₅.mem := hr₄.congr (by rw [hm₅])
  refine WP.ite (word s₄.mem p.B (8 * oStatus) == 1) (by simp [eval, hz₅]) ?_ ?_
  · intro _
    refine WP.mono (shapeOriginal_ok h₅ hd₅ havail)
      fun t ⟨ht, hdt, hvt, hst, hft, kt, hwords⟩ => ?_
    exact ⟨n, hn, ht, hdt, hr₅.congr (hwords _ (by decide)), fun _ => hvt,
      hs.trans hst, hf.trans hft, (kk.trans kt).mono (by decide)⟩
  · intro hno
    refine WP.block_nil ⟨n, hn, h₅, hd₅, hr₅, ?_, hs, hf, kk⟩
    intro he
    have hx : word s₄.mem p.B (8 * oStatus) = 1 := by simpa only [hm₅] using he
    simp only [hx, BEq.rfl, Bool.true_eq_false] at hno

end VG.Proof.Ffdh.X86_64.ParameterCandidate
