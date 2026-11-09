module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.PhaseRounds
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Algebra.Group.Nat.Defs

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
