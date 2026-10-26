module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateScreenMath
public import VerifiedGarbage.Spec.Ffdh.SievedCandidate
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateResidue
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ScreenedStream
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Data.Option.Basic

/-! The native controller's Boolean result is exactly the already merged candidate specification. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Proof.Ffdh.ParameterCandidate

def candidateAsSpec (p : CandidateParams) (answer : Option (Bool × List Byte)) : Option (Option Nat × List Byte) :=
  answer.map (fun (pass, tail) => (if pass then some p.candidate else none, tail))

theorem candidateScreen_spec (p : CandidateParams) (enough : p.length ≤ p.bytes.length) :
    candidateAsSpec p (candidateScreen p) = Spec.Ffdh.sievedParameterCandidate p.bits p.generator p.bytes := by
  unfold Spec.Ffdh.sievedParameterCandidate
  rw [draw_of_le (len := (p.bits + 7) / 8) enough]
  simp only [bind, Option.bind_some]
  change candidateAsSpec p (candidateScreen p) =
    (if !(Spec.Ffdh.generationShape p.bits p.generator p.candidate && Spec.Ffdh.primeShape p.candidate &&
      Spec.Ffdh.primeShape ((p.candidate - 1) / 2) &&
      !Spec.RsaKeyGen.obviouslyComposite p.bits p.candidate &&
      !Spec.RsaKeyGen.obviouslyComposite p.bits ((p.candidate - 1) / 2)) then some (none, p.bytes.drop p.length) else do
      let (pass, tail) ← Spec.Ffdh.screenedParameterWitnesses p.candidate ((p.candidate - 1) / 2) (p.bytes.drop p.length)
      pure (if pass then some p.candidate else none, tail))
  have reorder (a b c d e : Bool) : (a && b && c && d && e) = (a && (b && d) && (c && e)) := by
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> rfl
  rw [reorder]
  have halfBits : Spec.RsaKeyGen.bitLength ((p.candidate - 1) / 2) = p.bits - 1 :=
    VG.Proof.Ffdh.ParameterCandidate.half_bitLength (bits := p.bits)
      (by have := p.minBits; omega) (Spec.Rsa.os2ip (p.bytes.take p.length))
  unfold candidateScreen candidateScreenP candidateScreenQ
  by_cases gen : Spec.Ffdh.generationShape p.bits p.generator p.candidate = true
  · by_cases pp : (Spec.Ffdh.primeShape p.candidate && !Spec.RsaKeyGen.obviouslyComposite p.bits p.candidate) = true
    · by_cases qp : (Spec.Ffdh.primeShape ((p.candidate - 1) / 2) && !Spec.RsaKeyGen.obviouslyComposite p.bits ((p.candidate - 1) / 2)) = true
      · simp only [gen, pp, qp, Bool.true_and, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
        rw [← screenedChecks_eq ((Bool.and_eq_true _ _).mp pp).1 ((Bool.and_eq_true _ _).mp qp).1]
        unfold screenedChecks
        rw [p.candidate_bits, halfBits]
        unfold candidateTests screenedTests continueWitnesses witnessRemaining
        simp only [limitedPhase, limitedChecks, candidatePhase, phaseBits, Bool.false_eq_true, ite_false,
          ite_true, Nat.sub_zero]
        cases first : checkWitnesses p.candidate 1 (p.bytes.drop p.length) with
        | none => rfl
        | some pair =>
          obtain ⟨pass, tail⟩ := pair
          cases pass with
          | false => rfl
          | true =>
            dsimp only [bind, Option.bind_some, Bool.not_true, Bool.false_eq_true, ite_false]
            cases q : checkWitnesses ((p.candidate - 1) / 2) (Spec.Ffdh.primeChecks (p.bits - 1)) tail with
            | none => rfl
            | some pair =>
              obtain ⟨pass, rest⟩ := pair
              cases pass with
              | false => rfl
              | true =>
                dsimp only [bind, Option.bind_some, Bool.not_true, Bool.false_eq_true, ite_false]
                cases checkWitnesses p.candidate (Spec.Ffdh.primeChecks p.bits - 1) rest with
                | none => rfl
                | some pair => obtain ⟨pass, tail⟩ := pair; rfl
      · have nq : (Spec.Ffdh.primeShape ((p.candidate - 1) / 2) && !Spec.RsaKeyGen.obviouslyComposite p.bits ((p.candidate - 1) / 2)) = false := Bool.eq_false_iff.mpr qp
        simp [gen, pp, nq, candidateAsSpec, candidateRejected]
    · have np : (Spec.Ffdh.primeShape p.candidate && !Spec.RsaKeyGen.obviouslyComposite p.bits p.candidate) = false := Bool.eq_false_iff.mpr pp
      simp [gen, np, candidateAsSpec, candidateRejected]
  · have ng : Spec.Ffdh.generationShape p.bits p.generator p.candidate = false := Bool.eq_false_iff.mpr gen
    simp [ng, candidateAsSpec, candidateRejected]

def candidateAnswer (p : CandidateParams) : Option (Bool × List Byte) :=
  if p.length ≤ p.bytes.length then candidateScreen p else none

theorem candidateAnswer_spec (p : CandidateParams) :
    candidateAsSpec p (candidateAnswer p) = Spec.Ffdh.sievedParameterCandidate p.bits p.generator p.bytes := by
  by_cases enough : p.length ≤ p.bytes.length
  · rw [candidateAnswer, ite_eq_left enough]
    exact candidateScreen_spec p enough
  · rw [candidateAnswer, ite_eq_right enough]
    unfold Spec.Ffdh.sievedParameterCandidate
    have short : p.bytes.length < (p.bits + 7) / 8 := by change p.bytes.length < p.length; omega
    rw [draw_of_short short]
    rfl

end VG.Proof.Ffdh.Arm.ParameterCandidate
