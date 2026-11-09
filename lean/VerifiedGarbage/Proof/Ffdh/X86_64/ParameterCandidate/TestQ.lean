module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PolicyResult

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.HalveOutput
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseSetup
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LoadOutput
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CheckPrime
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LeavePhase
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ModulusPolicy
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseRounds
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeOriginal
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
/-! # FFDH parameter generation on x86-64: the witness phases

`phaseTest_ok`: one modulus's witnesses, then what follows if they pass.
p's first witness (`testFirst_ok`), then q's (`testQ_ok`), then p's others
(`testP_ok`), after q's trial division (`sieveQ_ok`) and p's (`sieveP_ok`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64 (seqs)
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)

/-- What a stage leaves from the tape at `used`: the octets it read, the
status and rest of `R`, and p in the output buffer for status 1. -/
def PhasePost (p : CandidateP) (used : Nat) (R : Option (Bool × List Byte)) (s t : State) : Prop :=
  ∃ consumed, consumed ≤ (p.rand.drop used).length ∧ CandidateTape p (used + consumed) t ∧
    t.gpr .rdi = p.B ∧ TapeOutcome p used consumed R t.mem ∧
    (word t.mem p.B (8 * oStatus) = 1 → Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem p.op p.k) = p.P) ∧
    CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t

theorem phaseTest_ok (M : Mont) (R : R2Impl M) (K : Kernel)
    {p : CandidateP} {used : Nat} {s : State} {prep next : Prog isa} (q : Bool) (c : Checks)
    (nextR : List Byte → Option (Bool × List Byte))
    (h : CandidateTape p used s) (hodd : p.phaseValue q % 2 = 1)
    (hprep : WP isa prep s fun t => CandidateTape p used t ∧ t.gpr .rdi = p.B ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem p.op p.k) = p.phaseValue q ∧
      CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t)
    (hnext : ∀ u t, CandidateTape p u t → t.gpr .rdi = p.B → word t.mem p.B (8 * oStatus) = 1 →
      WP isa next t (PhasePost p u (nextR (p.rand.drop u)) t)) :
    WP isa (phaseTest M.mm R.code K.run prep q c next) s
      (PhasePost p used (thenPolicy (checkWitnesses (p.phaseValue q) (p.phaseChecks q c) (p.rand.drop used)) nextR) s) := by
  unfold phaseTest
  simp only [seqs]
  refine WP.seq (WP.mono hprep fun s₁ ⟨h₁, hd₁, hv₁, hs₁, hf₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (phaseSetup_state_ok h₁ hd₁ q c)
    fun s₂ ⟨mi, h₂, hg₂, hp₂, hs₂, hf₂, k₂, ho₂⟩ => ?_)
  refine WP.seq (WP.mono (loadOutput_ok h₂ hg₂ hp₂ (by rw [ho₂]; exact hv₁))
    fun s₃ ⟨h₃, hg₃, hp₃, hn₃, hs₃, hf₃, k₃, _⟩ => ?_)
  refine WP.seq (WP.mono (modulusPolicy_ok M R K h₃ hg₃ hp₃ hn₃ hodd)
    fun s₄ ⟨n, hn, h₄, hd₄, hl₄, hr₄, hs₄, hf₄, k₄⟩ => ?_)
  refine WP.seq (WP.mono (leaveStatus_ok h₄ hd₄ hl₄)
    fun s₅ ⟨h₅, hd₅, hz₅, hm₅, hs₅, hf₅, k₅⟩ => ?_)
  have hs := (((hs₁.trans hs₂).trans hs₃).trans hs₄).trans hs₅
  have hf := (((hf₁.trans hf₂).trans hf₃).trans hf₄).trans hf₅
  have kk : Keep (.rdi :: mmRegs) s s₅ := ((((k₁.trans k₂).trans k₃).trans k₄).trans k₅).mono (by decide)
  have hr₅ : PhaseOutcome p used n q c s₅.mem := hr₄.congr (by rw [hm₅])
  refine WP.ite (word s₄.mem p.B (8 * oStatus) == 1) (by simp [eval, hz₅]) ?_ ?_
  · intro hyes
    have hy : word s₅.mem p.B (8 * oStatus) = 1 := by rw [hm₅]; exact beq_iff_eq.mp hyes
    refine WP.mono (hnext _ _ h₅ hd₅ hy) fun t ⟨k, hk, ht, hdt, hrt, hvt, hst, hft, kt⟩ => ?_
    refine ⟨n + k, ?_, ?_, hdt, tape_then hr₅ hy hrt, hvt,
      hs.trans hst, hf.trans hft, (kk.trans kt).mono (by decide)⟩
    · rw [List.length_drop] at hk hn ⊢; omega_using [hk, hn, h.bound]
    · simpa only [Nat.add_assoc] using ht
  · intro hno
    have hnot : word s₅.mem p.B (8 * oStatus) ≠ 1 := by
      intro he; rw [hm₅] at he; simp [he] at hno
    exact WP.block_nil ⟨n, hn, h₅, hd₅, tape_stop hr₅ hnot,
      fun he => False.elim (hnot he), hs, hf, kk⟩

theorem thenPolicy_true (r : Option (Bool × List Byte)) : thenPolicy r (fun x => some (true, x)) = r := by
  unfold thenPolicy
  cases r with
  | none => rfl
  | some ar => obtain ⟨pass, rest⟩ := ar; cases pass <;> rfl

theorem CandidateP.odd_P (p : CandidateP) (hb : 2 ≤ p.bits) : p.phaseValue false % 2 = 1 :=
  (VG.Proof.Ffdh.ParameterCandidate.candidate_shape (bits := p.bits) hb _).1

theorem shape_prep {p : CandidateP} {used : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B) (havail : p.k ≤ p.rand.length) :
    WP isa shapeOriginal s fun t => CandidateTape p used t ∧ t.gpr .rdi = p.B ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem p.op p.k) = p.phaseValue false ∧
      CandidateSaved p s.mem t.mem ∧ CandidateFrame p s.mem t.mem ∧ Keep (.rdi :: mmRegs) s t :=
  WP.mono (shapeOriginal_ok h hdi havail) fun _ ⟨ht, hd, hv, hs, hf, k, _⟩ =>
    ⟨ht, hd, hv, hs, hf, k.mono (by decide)⟩

theorem testP_ok (M : Mont) (R : R2Impl M) (K : Kernel)
    {p : CandidateP} {used : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B) (havail : p.k ≤ p.rand.length) :
    WP isa (testP M.mm R.code K.run) s (PhasePost p used (policyRest p (p.rand.drop used)) s) := by
  have hr : policyRest p (p.rand.drop used) =
      thenPolicy (checkWitnesses (p.phaseValue false) (p.phaseChecks false .rest) (p.rand.drop used))
        (fun x => some (true, x)) := by
    rw [thenPolicy_true]; rfl
  rw [hr]
  refine phaseTest_ok M R K false .rest _ h (p.odd_P (by omega_using [h.base.bits1])) (shape_prep h hdi havail) ?_
  intro u t ht hdt hy
  refine WP.mono (shapeOriginal_ok ht hdt havail) fun t' ⟨ht', hdt', hvt', hst', hft', kt', hwords⟩ => ?_
  have hy' : word t'.mem p.B (8 * oStatus) = 1 := (hwords _ (by decide)).trans hy
  exact ⟨0, Nat.zero_le _, by simpa only [Nat.add_zero] using ht', hdt', by simp [TapeOutcome, hy'],
    fun _ => hvt', hst', hft', kt'.mono (by decide)⟩

theorem testQ_ok (M : Mont) (R : R2Impl M) (K : Kernel)
    {p : CandidateP} {used : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B) (havail : p.k ≤ p.rand.length)
    (hq : p.Q % 2 = 1) :
    WP isa (testQ M.mm R.code K.run) s (PhasePost p used (policyQ p (p.rand.drop used)) s) := by
  refine phaseTest_ok M R K true .all _ h hq ?_ fun u t ht hdt _ => testP_ok M R K ht hdt havail
  refine WP.seq (WP.mono (shapeOriginal_ok h hdi havail) fun s₁ ⟨h₁, hd₁, hv₁, hs₁, hf₁, k₁, _⟩ => ?_)
  exact WP.mono (halveOutput_ok h₁ hd₁ hv₁) fun t ⟨ht, hd, hv, hs, hf, k⟩ =>
    ⟨ht, hd, hv, hs₁.trans hs, hf₁.trans hf, (k₁.trans k).mono (by decide)⟩

theorem testFirst_ok (M : Mont) (R : R2Impl M) (K : Kernel)
    {p : CandidateP} {used : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B) (havail : p.k ≤ p.rand.length)
    (hq : p.Q % 2 = 1) :
    WP isa (testFirst M.mm R.code K.run) s (PhasePost p used (policyFirst p (p.rand.drop used)) s) :=
  phaseTest_ok M R K false .first _ h (p.odd_P (by omega_using [h.base.bits1])) (shape_prep h hdi havail)
    fun u t ht hdt _ => testQ_ok M R K ht hdt havail hq

theorem sieveP_ok (M : Mont) (R : R2Impl M) (K : Kernel)
    {p : CandidateP} {used : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B) (havail : p.k ≤ p.rand.length)
    (hq : p.Q % 2 = 1) :
    WP isa (sieveP M.mm R.code K.run) s (PhasePost p used (sievedP p (p.rand.drop used)) s) := by
  unfold sieveP
  simp only [seqs]
  refine WP.seq (WP.mono (shapeOriginal_ok h hdi havail) fun s₁ ⟨h₁, hd₁, hv₁, hs₁, hf₁, k₁, _⟩ => ?_)
  refine WP.seq (WP.mono (phaseSetup_state_ok h₁ hd₁ false .all)
    fun s₂ ⟨mi, h₂, hg₂, hp₂, hs₂, hf₂, k₂, ho₂⟩ => ?_)
  refine WP.seq (WP.mono (loadOutput_ok h₂ hg₂ hp₂ (by rw [ho₂]; exact hv₁))
    fun s₃ ⟨h₃, hg₃, hp₃, hn₃, hs₃, hf₃, k₃, _⟩ => ?_)
  refine WP.seq (WP.mono (primeCheck_state_ok h₃ hg₃ hp₃ hn₃)
    fun s₄ ⟨h₄, hg₄, hp₄, hn₄, hz₄, hs₄, hf₄, k₄, _⟩ => ?_)
  have hs := ((hs₁.trans hs₂).trans hs₃).trans hs₄
  have hf := ((hf₁.trans hf₂).trans hf₃).trans hf₄
  have kk : Keep (.rdi :: mmRegs) s s₄ := (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)
  refine WP.ite (p.sieved p.P) (by simpa [eval, CandidateP.phaseValue, CandidateP.sieved] using hz₄) ?_ ?_
  · intro hshape
    refine WP.seq (WP.mono (leavePhase_ok h₄ hg₄.rdi hp₄.link)
      fun s₅ ⟨h₅, hd₅, _, hs₅, hf₅, k₅⟩ => ?_)
    refine WP.mono (testFirst_ok M R K h₅ hd₅ havail hq)
      fun t ⟨n, hn, ht, hdt, hr, hvt, hst, hft, kt⟩ => ?_
    exact ⟨n, hn, ht, hdt, by simpa only [sievedP, hshape, ite_true] using hr, hvt,
      (hs.trans hs₅).trans hst, (hf.trans hf₅).trans hft, ((kk.trans k₅).trans kt).mono (by decide)⟩
  · intro hshape
    refine WP.mono (innerStatus_ok h₄ hg₄.rdi hp₄.link (n := 2) (by decide))
      fun t ⟨ht, hdt, hst, hsave, hframe, kt⟩ => ?_
    exact ⟨0, Nat.zero_le _, by simpa only [Nat.add_zero] using ht, hdt,
      by simpa only [sievedP, hshape, Bool.false_eq_true, ite_false] using tape_reject (used := used) hst,
      fun he => by rw [hst] at he; contradiction,
      hs.trans hsave, hf.trans hframe, (kk.trans kt).mono (by decide)⟩

theorem sieveQ_ok (M : Mont) (R : R2Impl M) (K : Kernel)
    {p : CandidateP} {used : Nat} {s : State}
    (h : CandidateTape p used s) (hdi : s.gpr .rdi = p.B) (havail : p.k ≤ p.rand.length)
    (hv : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem p.op p.k) = p.P) :
    WP isa (sieveQ M.mm R.code K.run) s (PhasePost p used (sievedPolicy p (p.rand.drop used)) s) := by
  unfold sieveQ
  simp only [seqs]
  refine WP.seq (WP.mono (halveOutput_ok h hdi hv) fun s₁ ⟨h₁, hd₁, hv₁, hs₁, hf₁, k₁⟩ => ?_)
  refine WP.seq (WP.mono (phaseSetup_state_ok h₁ hd₁ true .all)
    fun s₂ ⟨mi, h₂, hg₂, hp₂, hs₂, hf₂, k₂, ho₂⟩ => ?_)
  refine WP.seq (WP.mono (loadOutput_ok h₂ hg₂ hp₂ (by rw [ho₂]; exact hv₁))
    fun s₃ ⟨h₃, hg₃, hp₃, hn₃, hs₃, hf₃, k₃, _⟩ => ?_)
  refine WP.seq (WP.mono (primeCheck_state_ok h₃ hg₃ hp₃ hn₃)
    fun s₄ ⟨h₄, hg₄, hp₄, hn₄, hz₄, hs₄, hf₄, k₄, _⟩ => ?_)
  have hs := ((hs₁.trans hs₂).trans hs₃).trans hs₄
  have hf := ((hf₁.trans hf₂).trans hf₃).trans hf₄
  have kk : Keep (.rdi :: mmRegs) s s₄ := (((k₁.trans k₂).trans k₃).trans k₄).mono (by decide)
  refine WP.ite (p.sieved p.Q) (by simpa [eval, CandidateP.phaseValue, CandidateP.sieved] using hz₄) ?_ ?_
  · intro hshape
    refine WP.seq (WP.mono (leavePhase_ok h₄ hg₄.rdi hp₄.link)
      fun s₅ ⟨h₅, hd₅, _, hs₅, hf₅, k₅⟩ => ?_)
    refine WP.mono (sieveP_ok M R K h₅ hd₅ havail (odd_of_sieved hshape))
      fun t ⟨n, hn, ht, hdt, hr, hvt, hst, hft, kt⟩ => ?_
    exact ⟨n, hn, ht, hdt, by simpa only [sievedPolicy, hshape, ite_true] using hr, hvt,
      (hs.trans hs₅).trans hst, (hf.trans hf₅).trans hft, ((kk.trans k₅).trans kt).mono (by decide)⟩
  · intro hshape
    refine WP.mono (innerStatus_ok h₄ hg₄.rdi hp₄.link (n := 2) (by decide))
      fun t ⟨ht, hdt, hst, hsave, hframe, kt⟩ => ?_
    exact ⟨0, Nat.zero_le _, by simpa only [Nat.add_zero] using ht, hdt,
      by simpa only [sievedPolicy, hshape, Bool.false_eq_true, ite_false] using tape_reject (used := used) hst,
      fun he => by rw [hst] at he; contradiction,
      hs.trans hsave, hf.trans hframe, (kk.trans kt).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
