module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Start
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseSetup
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LoadOutput
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CheckPrime
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.LeavePhase
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ModulusPolicy
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Consume
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CheckGenerator
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Screen
import Mathlib.Algebra.Group.Nat.Defs
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.Contract
import Mathlib.Basic.IsEmpty.Defs
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ScreenedStream

/-! ### `Ffdh.X86_64.ParameterCandidate.PolicyResult`, which only this module used -/

section

/-! # FFDH parameter generation on x86-64: compose the phases' tape results

p's first witness, then q's, then p's others (`policyFirst`), as
`Spec.Ffdh.screenedParameterWitnesses` draws them.
-/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.Proof.Bignum VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)

def TapeOutcome (p : CandidateP) (used consumed : Nat) (result : Option (Bool × List Byte)) (m : Mem) : Prop :=
  match result with
  | none => word m p.B (8 * oStatus) = 0
  | some (pass, rest) => word m p.B (8 * oStatus) = BitVec.ofNat 64 (if pass then 1 else 2) ∧
      rest = p.rand.drop (used + consumed)

/-- A phase's result, then `next` on the rest of the tape if it passed. -/
def thenPolicy (r : Option (Bool × List Byte)) (next : List Byte → Option (Bool × List Byte)) :
    Option (Bool × List Byte) := do
  let (pass, rest) ← r
  if !pass then return (false, rest)
  next rest

/-- p's other witnesses. -/
def policyRest (p : CandidateP) (r : List Byte) : Option (Bool × List Byte) :=
  checkWitnesses p.P (p.phaseChecks false .rest) r

/-- q's witnesses, then p's others. -/
def policyQ (p : CandidateP) (r : List Byte) : Option (Bool × List Byte) :=
  thenPolicy (checkWitnesses p.Q (p.phaseChecks true .all) r) (policyRest p)

/-- p's first witness, then q's, then p's others. -/
def policyFirst (p : CandidateP) (r : List Byte) : Option (Bool × List Byte) :=
  thenPolicy (checkWitnesses p.P (p.phaseChecks false .first) r) (policyQ p)

/-- p's whole trial division, then the witnesses. -/
def sievedP (p : CandidateP) (r : List Byte) : Option (Bool × List Byte) :=
  if p.sieved p.P then policyFirst p r else some (false, r)

/-- q's trial division, then p's, then the witnesses. -/
def sievedPolicy (p : CandidateP) (r : List Byte) : Option (Bool × List Byte) :=
  if p.sieved p.Q then sievedP p r else some (false, r)

theorem tape_reject {p : CandidateP} {used : Nat} {m : Mem} (hstatus : word m p.B (8 * oStatus) = 2) :
    TapeOutcome p used 0 (some (false, p.rand.drop used)) m := by
  simp [TapeOutcome, hstatus]

theorem tape_stop {p : CandidateP} {used n : Nat} {q : Bool} {c : Checks} {m : Mem}
    {next : List Byte → Option (Bool × List Byte)}
    (h : PhaseOutcome p used n q c m) (hn : word m p.B (8 * oStatus) ≠ 1) :
    TapeOutcome p used n
      (thenPolicy (checkWitnesses (p.phaseValue q) (p.phaseChecks q c) (p.rand.drop used)) next) m := by
  unfold PhaseOutcome at h
  unfold thenPolicy
  cases he : checkWitnesses (p.phaseValue q) (p.phaseChecks q c) (p.rand.drop used) with
  | none => simpa [he, TapeOutcome] using h
  | some ar =>
    obtain ⟨pass, rest⟩ := ar
    cases pass
    · simpa [he, TapeOutcome] using h
    · simp only [he] at h
      exact False.elim (hn h.1)

theorem tape_then {p : CandidateP} {used n k : Nat} {q : Bool} {c : Checks} {m m' : Mem}
    {next : List Byte → Option (Bool × List Byte)}
    (h : PhaseOutcome p used n q c m) (hy : word m p.B (8 * oStatus) = 1)
    (hk : TapeOutcome p (used + n) k (next (p.rand.drop (used + n))) m') :
    TapeOutcome p used (n + k)
      (thenPolicy (checkWitnesses (p.phaseValue q) (p.phaseChecks q c) (p.rand.drop used)) next) m' := by
  unfold PhaseOutcome at h
  cases he : checkWitnesses (p.phaseValue q) (p.phaseChecks q c) (p.rand.drop used) with
  | none => simp only [he] at h; simp [hy] at h
  | some ar =>
    obtain ⟨pass, rest⟩ := ar
    cases pass
    · simp only [he] at h; simp [hy] at h
    · simp only [he] at h
      unfold thenPolicy
      simp only [Bool.not_true, Bool.false_eq_true, ite_false, bind, Option.bind_some, h.2]
      unfold TapeOutcome at hk ⊢
      simpa only [Nat.add_assoc] using hk

end VG.Proof.Ffdh.X86_64.ParameterCandidate

end

end

/-! ### `Ffdh.X86_64.ParameterCandidate.CandidateTest`, which only this module used -/

section

/-! ### `Ffdh.X86_64.ParameterCandidate.TestQ`, which only this module used -/

section

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

end

end


/-! # FFDH parameter generation on x86-64: the complete candidate test -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64 (seqs)
open VG.Impl.Rsa.X86_64.Crt
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64

def candidateTail (p : CandidateP) (r : List Byte) : Option (Bool × List Byte) :=
  if p.congruent && earlyOk p.P then sievedPolicy p r
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
  refine WP.seq (WP.mono (consumeCandidate_ok h₁ hd₁ havail) fun s₂₀ ⟨h₂₀, hs₂₀, hf₂₀, k₂₀, ho₂₀⟩ => ?_)
  have hd₂₀ : s₂₀.gpr .rdi = p.B := (k₂₀.gpr (by decide)).trans hd₁
  -- The screen on p's octets, before any workspace.
  refine WP.seq (WP.mono (outerScreen_ok h₂₀ hd₂₀) fun s₂ ⟨hzs, hms, ks⟩ => ?_)
  obtain ⟨h₂, hs₂', hf₂'⟩ := h₂₀.same_mem hms ks (by decide)
  have hs₂ := hs₂₀.trans hs₂'
  have hf₂ := hf₂₀.trans hf₂'
  have k₂ : Keep mmRegs s₁ s₂ := (k₂₀.trans ks).mono (by decide)
  have ho₂ : Spec.Rsa.bytesAt s₂.mem p.op p.k = Spec.Rsa.bytesAt s₁.mem p.op p.k := by rw [hms]; exact ho₂₀
  have hd₂ : s₂.gpr .rdi = p.B := (ks.gpr (by decide)).trans hd₂₀
  have hscr : outP p s₂₀.mem = p.P := by unfold outP; rw [ho₂₀]; exact hv₁
  refine WP.ite (screen p.gen p.P) (by simp [eval, hzs, hscr]) (fun hscreen => ?_) (fun hscreen => ?_)
  rotate_left
  · have hsc : screen p.gen p.P = false := by simpa using hscreen
    refine WP.mono (status_ok h₂ hd₂ (n := 2) (by decide))
      fun t ⟨ht, hdt, hstatus, hst, hft, kt⟩ => ?_
    refine ⟨0, Nat.zero_le _, by simpa only [Nat.add_zero] using ht, hdt, ?_,
      fun he => by rw [hstatus] at he; contradiction, (hs₁.trans hs₂).trans hst, (hf₁.trans hf₂).trans hft,
      ((k₁.trans k₂).trans kt).mono (by decide)⟩
    simp [candidateTail, CandidateP.congruent, hsc, TapeOutcome, hstatus]
  unfold candidateFilter
  simp only [seqs]
  refine WP.seq (WP.mono (phaseSetup_state_ok h₂ hd₂ false .all)
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
  refine WP.ite p.congruent (by simp [eval, hz₅]) ?_ ?_
  · intro hgen
    refine WP.seq (WP.mono (earlyCheck_state_ok h₅ hg₅ hp₅ hn₅)
      fun s₆ ⟨h₆, hg₆, hp₆, _, hz₆, hs₆, hf₆, k₆, ho₆⟩ => ?_)
    have hs'' := hs'.trans hs₆
    have hf'' := hf'.trans hf₆
    have kk'' : Keep (.rdi :: mmRegs) s s₆ := (kk'.trans k₆).mono (by decide)
    refine WP.ite (earlyOk p.P) (by simpa [eval, CandidateP.phaseValue] using hz₆) ?_ ?_
    · intro hprime
      refine WP.seq (WP.mono (leavePhase_ok h₆ hg₆.rdi hp₆.link)
        fun s₇ ⟨h₇, hd₇, hm₇, hs₇, hf₇, k₇⟩ => ?_)
      refine WP.mono (sieveQ_ok M R K h₇ hd₇ havail (by rw [hm₇, ho₆, hm₅]; exact hv₄))
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

end

end

/-! # FFDH parameter generation on x86-64: the complete callable body -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/ParameterCandidate/ResultBridge.lean`, which only this module imported.
section

/-! # FFDH parameter generation on x86-64: relate the native policy to the specification -/

section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum
open VG.Proof.Ffdh.ParameterCandidate

theorem CandidateBase.candidate_result {p : CandidateP} {s : State} (h : CandidateBase p s)
    (havail : p.k ≤ p.rand.length) :
    Spec.Ffdh.sievedParameterCandidate p.bits p.gen p.rand =
      (candidateTail p (p.rand.drop p.k)).map (fun x => (if x.1 then some p.P else none, x.2)) := by
  unfold Spec.Ffdh.sievedParameterCandidate
  rw [← h.len, draw_of_le havail]
  simp only [bind, Option.bind_some]
  change (do
    if !(Spec.Ffdh.generationShape p.bits p.gen p.P && Spec.Ffdh.primeShape p.P && Spec.Ffdh.primeShape p.Q &&
        !Spec.RsaKeyGen.obviouslyComposite p.bits p.P && !Spec.RsaKeyGen.obviouslyComposite p.bits p.Q) then
      return (none, p.rand.drop p.k)
    let (pass, rest) ← Spec.Ffdh.screenedParameterWitnesses p.P p.Q (p.rand.drop p.k)
    return (if pass then some p.P else none, rest)) = _
  have hpodd : p.P % 2 = 1 :=
    (candidate_shape (bits := p.bits) (by omega_using [h.bits1]) _).1
  have hpbits : Spec.RsaKeyGen.bitLength p.P = p.phaseBits false := (h.phase_bitLength false hpodd).1
  have hcond : (Spec.Ffdh.generationShape p.bits p.gen p.P && Spec.Ffdh.primeShape p.P &&
      Spec.Ffdh.primeShape p.Q && !Spec.RsaKeyGen.obviouslyComposite p.bits p.P &&
      !Spec.RsaKeyGen.obviouslyComposite p.bits p.Q) =
      ((p.congruent && p.sieved p.P) && p.sieved p.Q) := by
    rw [congruent_sieved h.bits1 h.gen]
    unfold CandidateP.sieved
    cases Spec.Ffdh.generationShape p.bits p.gen p.P <;> cases Spec.Ffdh.primeShape p.P <;>
      cases Spec.Ffdh.primeShape p.Q <;> cases Spec.RsaKeyGen.obviouslyComposite p.bits p.P <;>
      cases Spec.RsaKeyGen.obviouslyComposite p.bits p.Q <;> rfl
  -- `earlyOk` rejects only what the whole sieve of p rejects.
  have hearly : p.sieved p.P = true → earlyOk p.P = true :=
    earlyOk_of_sieved (by simpa [CandidateP.phaseValue] using h.phase_large false)
  have htail : candidateTail p (p.rand.drop p.k) =
      if (p.congruent && p.sieved p.P) && p.sieved p.Q then policyFirst p (p.rand.drop p.k)
      else some (false, p.rand.drop p.k) := by
    unfold candidateTail sievedPolicy sievedP
    cases hc : p.congruent <;> cases hs : p.sieved p.P <;> cases hq : p.sieved p.Q <;>
      cases ho : earlyOk p.P <;> simp_all
  rw [hcond, htail]
  by_cases hgp : (p.congruent && p.sieved p.P) = true
  · by_cases hq : p.sieved p.Q = true
    · have hqodd : p.Q % 2 = 1 := odd_of_sieved hq
      have hqbits : Spec.RsaKeyGen.bitLength p.Q = p.phaseBits true := (h.phase_bitLength true hqodd).1
      have hpshape : Spec.Ffdh.primeShape p.P = true := by
        unfold CandidateP.sieved at hgp
        exact ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hgp).2).1
      have hqshape : Spec.Ffdh.primeShape p.Q = true := by
        unfold CandidateP.sieved at hq
        exact ((Bool.and_eq_true _ _).mp hq).1
      have hpol : policyFirst p (p.rand.drop p.k) =
          Spec.Ffdh.screenedParameterWitnesses p.P p.Q (p.rand.drop p.k) := by
        rw [← screenedChecks_eq hpshape hqshape]
        unfold policyFirst policyQ policyRest CandidateP.phaseChecks
        rw [← hqbits, ← hpbits]
        rfl
      simp only [hgp, hq, Bool.and_self, Bool.not_true, Bool.false_eq_true, ite_false,
        ite_true, hpol]
      cases Spec.Ffdh.screenedParameterWitnesses p.P p.Q (p.rand.drop p.k) with
      | none => rfl
      | some ar => obtain ⟨pass, rest⟩ := ar; cases pass <;> rfl
    · have hqf : p.sieved p.Q = false := Bool.eq_false_iff.mpr hq
      simp [hgp, hqf]
  · have hgpf : (p.congruent && p.sieved p.P) = false :=
      Bool.eq_false_iff.mpr hgp
    simp [hgpf]

end VG.Proof.Ffdh.X86_64.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/ParameterCandidate/NativeResult.lean`, which only this module imported.
section

/-! # FFDH parameter generation on x86-64: the public status and consumed prefix -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.Proof.Bignum VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Ffdh.ParameterCandidate

def NativeResult (p : CandidateP) (used : Nat) (m : Mem) : Prop :=
  let r := Spec.Ffdh.sievedParameterCandidate p.bits p.gen p.rand
  word m p.B (8 * oStatus) = BitVec.ofNat 64 (Proof.Ffdh.candidateStatus r) ∧
    (match r with | none => True | some (_, rest) => rest = p.rand.drop used) ∧
    (∀ n rest, r = some (some n, rest) → n = p.P)

theorem CandidateBase.nativeResult {p : CandidateP} {s : VG.X86_64.State} {n : Nat} {m : Mem}
    (h : CandidateBase p s) (havail : p.k ≤ p.rand.length)
    (hr : TapeOutcome p p.k n (candidateTail p (p.rand.drop p.k)) m) :
    NativeResult p (p.k + n) m := by
  unfold NativeResult
  rw [h.candidate_result havail]
  cases he : candidateTail p (p.rand.drop p.k) with
  | none => simpa [he, TapeOutcome, Proof.Ffdh.candidateStatus] using hr
  | some ar =>
    obtain ⟨pass, rest⟩ := ar
    cases pass
    · simp only [he, TapeOutcome] at hr
      simp [Proof.Ffdh.candidateStatus, hr]
    · simp only [he, TapeOutcome] at hr
      simp [Proof.Ffdh.candidateStatus, hr]

theorem CandidateBase.short_result {p : CandidateP} {s : VG.X86_64.State}
    (h : CandidateBase p s) (hshort : p.rand.length < p.k) :
    Spec.Ffdh.sievedParameterCandidate p.bits p.gen p.rand = none := by
  unfold Spec.Ffdh.sievedParameterCandidate
  rw [← h.len, draw_of_short hshort]
  rfl

end VG.Proof.Ffdh.X86_64.ParameterCandidate
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64

def BodyPost (s t : State) : Prop :=
  let p := candidateOfState s
  ∃ used, CandidateTape p used t ∧ t.gpr .rdi = p.B ∧ NativeResult p used t.mem ∧
    (word t.mem p.B (8 * oStatus) = 1 → Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem p.op p.k) = p.P) ∧
    (∀ i < 6, word t.mem p.B (8 * i) = s.gpr (saved.getD i .rax)) ∧ Keep (.rdi :: mmRegs) s t

theorem body_ok (M : Mont) (R : R2Impl M) (K : Kernel) {s : State} (c : PcCtx s) :
    WP isa (body M.mm R.code K.run) s (BodyPost s) := by
  let p := candidateOfState s
  change WP isa (body M.mm R.code K.run) s (fun t => ∃ used,
    CandidateTape p used t ∧ t.gpr .rdi = p.B ∧ NativeResult p used t.mem ∧
      (word t.mem p.B (8 * oStatus) = 1 → Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem p.op p.k) = p.P) ∧
      (∀ i < 6, word t.mem p.B (8 * i) = s.gpr (saved.getD i .rax)) ∧ Keep (.rdi :: mmRegs) s t)
  unfold body
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (candidateEntry_base c) fun u ⟨hu, hdu, hstatus, _, hsaved, ku⟩ => ?_
  change CandidateTape p 0 u at hu
  change u.gpr .rdi = p.B at hdu
  change word u.mem p.B (8 * oStatus) = 0 at hstatus
  have hlen := hu.base.hdr (oLen, BitVec.ofNat 64 p.k) (by simp [CandidateP.headers])
  have hleft : word u.mem p.B (8 * oRandLeft) = BitVec.ofNat 64 p.rand.length := by simpa using hu.left
  have hrd : ∀ j < 32, InRegions (u.rd ++ u.wr) (off p.B (8 * j)) 8 :=
    fun j hj => hu.base.scr.ld (by omega_using [hj, hu.base.header_room])
  refine WP.mono (WP.keep [.rax] (Q := fun v => v.cf = some (decide (p.rand.length < p.k)) ∧ v.mem = u.mem)
    (by
      xrun [State.ea, hdr, hdrOff, hdu, hleft, hlen, hrd oRandLeft (by decide), hrd oLen (by decide)]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hu.base.randLen,
        Nat.mod_eq_of_lt (show p.k < 2 ^ 64 by omega_using [hu.base.widths.2])]) rfl)
    fun v ⟨⟨hcf, hm⟩, kv⟩ => ?_
  obtain ⟨hv, _, _⟩ := hu.same_mem hm kv (by decide)
  have hdv : v.gpr .rdi = p.B := (kv.gpr (by decide)).trans hdu
  have hsavedv : ∀ i < 6, word v.mem p.B (8 * i) = s.gpr (saved.getD i .rax) := by
    intro i hi; rw [hm]; exact hsaved i hi
  have kk : Keep (.rdi :: mmRegs) s v := (ku.trans kv).mono (by decide)
  refine WP.ite (decide (p.rand.length < p.k)) (by simp [eval, hcf]) ?_ ?_
  · intro hshort
    have hr := hv.base.short_result (of_decide_eq_true hshort)
    have hstat : word v.mem p.B (8 * oStatus) = 0 := by rw [hm]; exact hstatus
    refine WP.block_nil ⟨0, hv, hdv, ?_, ?_, hsavedv, kk⟩
    · simp [NativeResult, hr, Proof.Ffdh.candidateStatus, hstat]
    · intro he; rw [hstat] at he; contradiction
  · intro havail
    refine WP.mono (testCandidate_ok M R K hv hdv (by omega_using [of_decide_eq_false havail]))
      fun t ⟨n, _, ht, hdt, hresult, hout, hs, _, kt⟩ => ?_
    exact ⟨p.k + n, ht, hdt, hv.base.nativeResult (by omega_using [of_decide_eq_false havail]) hresult,
      hout, fun i hi => (hs i (by omega_using [hi])).trans (hsavedv i hi), (kk.trans kt).mono (by decide)⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
