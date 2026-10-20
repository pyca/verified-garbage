module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseRounds
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter generation on x86-64: compose q and p tape results -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.Proof.Bignum VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Ffdh.ParameterCandidate (checkWitnesses)

def TapeOutcome (p : CandidateP) (used consumed : Nat) (result : Option (Bool × List Byte)) (m : Mem) : Prop :=
  match result with
  | none => word m p.B (8 * oStatus) = 0
  | some (pass, rest) => word m p.B (8 * oStatus) = BitVec.ofNat 64 (if pass then 1 else 2) ∧
      rest = p.rand.drop (used + consumed)

def qPolicy (p : CandidateP) (r : List Byte) : Option (Bool × List Byte) := do
  if !Spec.Ffdh.primeShape p.Q then return (false, r)
  let (pass, rest) ← checkWitnesses p.Q (Spec.Ffdh.primeChecks (p.phaseBits true)) r
  if !pass then return (false, rest)
  checkWitnesses p.P (Spec.Ffdh.primeChecks (p.phaseBits false)) rest

theorem PhaseOutcome.as_tape {p : CandidateP} {used n : Nat} {q : Bool} {m : Mem}
    (h : PhaseOutcome p used n q m) :
    TapeOutcome p used n (checkWitnesses (p.phaseValue q) (Spec.Ffdh.primeChecks (p.phaseBits q))
      (p.rand.drop used)) m := by
  unfold TapeOutcome PhaseOutcome at *
  exact h

theorem TapeOutcome.congr {p : CandidateP} {used n : Nat} {result : Option (Bool × List Byte)} {m m' : Mem}
    (h : TapeOutcome p used n result m)
    (hs : word m' p.B (8 * oStatus) = word m p.B (8 * oStatus)) : TapeOutcome p used n result m' := by
  unfold TapeOutcome at *
  simpa only [hs] using h

theorem qPolicy_reject {p : CandidateP} {used : Nat} {m : Mem}
    (hs : Spec.Ffdh.primeShape p.Q = false) (hstatus : word m p.B (8 * oStatus) = 2) :
    TapeOutcome p used 0 (qPolicy p (p.rand.drop used)) m := by
  simp [qPolicy, hs, TapeOutcome, hstatus]

theorem qPolicy_stop {p : CandidateP} {used n : Nat} {m : Mem}
    (hs : Spec.Ffdh.primeShape p.Q = true) (h : PhaseOutcome p used n true m)
    (hn : word m p.B (8 * oStatus) ≠ 1) :
    TapeOutcome p used n (qPolicy p (p.rand.drop used)) m := by
  unfold PhaseOutcome at h
  change (match checkWitnesses p.Q (Spec.Ffdh.primeChecks (p.phaseBits true)) (p.rand.drop used) with
    | none => word m p.B (8 * oStatus) = 0
    | some (pass, rest) => word m p.B (8 * oStatus) = BitVec.ofNat 64 (if pass then 1 else 2) ∧
        rest = p.rand.drop (used + n)) at h
  unfold qPolicy
  simp only [hs, Bool.not_true, Bool.false_eq_true, ite_false]
  cases he : checkWitnesses p.Q (Spec.Ffdh.primeChecks (p.phaseBits true)) (p.rand.drop used) with
  | none => simpa [he, TapeOutcome] using h
  | some ar =>
    obtain ⟨pass, rest⟩ := ar
    cases pass
    · simpa [he, TapeOutcome] using h
    · simp only [he] at h
      exact False.elim (hn h.1)

theorem qPolicy_pass {p : CandidateP} {used n k : Nat} {m m' : Mem}
    (hs : Spec.Ffdh.primeShape p.Q = true) (h : PhaseOutcome p used n true m)
    (hy : word m p.B (8 * oStatus) = 1) (hp : PhaseOutcome p (used + n) k false m') :
    TapeOutcome p used (n + k) (qPolicy p (p.rand.drop used)) m' := by
  unfold PhaseOutcome at h
  change (match checkWitnesses p.Q (Spec.Ffdh.primeChecks (p.phaseBits true)) (p.rand.drop used) with
    | none => word m p.B (8 * oStatus) = 0
    | some (pass, rest) => word m p.B (8 * oStatus) = BitVec.ofNat 64 (if pass then 1 else 2) ∧
        rest = p.rand.drop (used + n)) at h
  cases he : checkWitnesses p.Q (Spec.Ffdh.primeChecks (p.phaseBits true)) (p.rand.drop used) with
  | none => simp only [he] at h; simp [hy] at h
  | some ar =>
    obtain ⟨pass, rest⟩ := ar
    cases pass
    · simp only [he] at h; simp [hy] at h
    · simp only [he] at h
      unfold qPolicy
      simp only [hs, Bool.not_true, Bool.false_eq_true, ite_false, he, bind, Option.bind_some, h.2]
      have ht := hp.as_tape
      change TapeOutcome p (used + n) k
        (checkWitnesses p.P (Spec.Ffdh.primeChecks (p.phaseBits false)) (p.rand.drop (used + n))) m' at ht
      unfold TapeOutcome at ht ⊢
      simpa only [Nat.add_assoc] using ht

end VG.Proof.Ffdh.X86_64.ParameterCandidate
