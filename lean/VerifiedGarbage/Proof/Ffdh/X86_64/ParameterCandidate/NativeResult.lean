module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CandidateTest
public import VerifiedGarbage.Spec.Ffdh.Contract

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ResultBridge
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Basic.IsEmpty.Defs

/-! # FFDH parameter generation on x86-64: the public status and consumed prefix -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.Proof.Bignum VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Ffdh.ParameterCandidate

def NativeResult (p : CandidateP) (used : Nat) (m : Mem) : Prop :=
  let r := Spec.Ffdh.parameterCandidate p.bits p.gen p.rand
  word m p.B (8 * oStatus) = BitVec.ofNat 64 (Spec.Ffdh.candidateStatus r) ∧
    (match r with | none => True | some (_, rest) => rest = p.rand.drop used) ∧
    (∀ n rest, r = some (some n, rest) → n = p.P)

theorem CandidateBase.nativeResult {p : CandidateP} {s : VG.X86_64.State} {n : Nat} {m : Mem}
    (h : CandidateBase p s) (havail : p.k ≤ p.rand.length)
    (hr : TapeOutcome p p.k n (candidateTail p (p.rand.drop p.k)) m) :
    NativeResult p (p.k + n) m := by
  unfold NativeResult
  rw [h.candidate_result havail]
  cases he : candidateTail p (p.rand.drop p.k) with
  | none => simpa [he, TapeOutcome, Spec.Ffdh.candidateStatus] using hr
  | some ar =>
    obtain ⟨pass, rest⟩ := ar
    cases pass
    · simp only [he, TapeOutcome] at hr
      simp [Spec.Ffdh.candidateStatus, hr]
    · simp only [he, TapeOutcome] at hr
      simp [Spec.Ffdh.candidateStatus, hr]

theorem CandidateBase.short_result {p : CandidateP} {s : VG.X86_64.State}
    (h : CandidateBase p s) (hshort : p.rand.length < p.k) :
    Spec.Ffdh.parameterCandidate p.bits p.gen p.rand = none := by
  rw [← checkedCandidate_eq]
  unfold checkedCandidate
  rw [← h.len, draw_of_short hshort]
  rfl

end VG.Proof.Ffdh.X86_64.ParameterCandidate
