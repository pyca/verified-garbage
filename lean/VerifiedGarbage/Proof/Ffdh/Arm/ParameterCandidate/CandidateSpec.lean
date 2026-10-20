module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateScreenMath
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateResidue
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.Omega

/-! The native controller's Boolean result is exactly the already merged candidate specification. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Proof.Ffdh.ParameterCandidate

def candidateAsSpec (p : CandidateParams) (answer : Option (Bool × List Byte)) : Option (Option Nat × List Byte) :=
  answer.map (fun (pass, tail) => (if pass then some p.candidate else none, tail))

theorem candidateScreen_spec (p : CandidateParams) (enough : p.length ≤ p.bytes.length) :
    candidateAsSpec p (candidateScreen p) = Spec.Ffdh.parameterCandidate p.bits p.generator p.bytes := by
  rw [← checkedCandidate_eq]
  unfold checkedCandidate
  rw [draw_of_le (len := (p.bits + 7) / 8) enough]
  simp only [bind, Option.bind_some]
  change candidateAsSpec p (candidateScreen p) =
    (if !(Spec.Ffdh.generationShape p.bits p.generator p.candidate && Spec.Ffdh.primeShape p.candidate &&
      Spec.Ffdh.primeShape ((p.candidate - 1) / 2)) then some (none, p.bytes.drop p.length) else do
      let (qpass, tail) ← checkWitnesses ((p.candidate - 1) / 2)
        (Spec.Ffdh.primeChecks (Spec.RsaKeyGen.bitLength ((p.candidate - 1) / 2))) (p.bytes.drop p.length)
      if !qpass then some (none, tail) else do
        let (ppass, tail) ← checkWitnesses p.candidate (Spec.Ffdh.primeChecks (Spec.RsaKeyGen.bitLength p.candidate)) tail
        pure (if ppass then some p.candidate else none, tail))
  have halfBits : Spec.RsaKeyGen.bitLength ((p.candidate - 1) / 2) = p.bits - 1 :=
    VG.Proof.Ffdh.ParameterCandidate.half_bitLength (bits := p.bits)
      (by have := p.minBits; omega) (Spec.Rsa.os2ip (p.bytes.take p.length))
  rw [p.candidate_bits, halfBits]
  unfold candidateScreen candidateScreenP candidateScreenQ
  by_cases gen : Spec.Ffdh.generationShape p.bits p.generator p.candidate = true
  · by_cases pp : Spec.Ffdh.primeShape p.candidate = true
    · by_cases qp : Spec.Ffdh.primeShape ((p.candidate - 1) / 2) = true
      · simp only [gen, pp, qp, Bool.true_and, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
        unfold candidateTests witnessRemaining
        simp only [candidatePhase, phaseBits, ite_true, Nat.sub_zero]
        cases hq : checkWitnesses ((p.candidate - 1) / 2) (Spec.Ffdh.primeChecks (p.bits - 1)) (p.bytes.drop p.length) with
        | none => rfl
        | some pair =>
          obtain ⟨pass, tail⟩ := pair
          cases pass with
          | false => rfl
          | true =>
            change candidateAsSpec p (checkWitnesses p.candidate (Spec.Ffdh.primeChecks p.bits) tail) =
              (do let (pass, rest) ← checkWitnesses p.candidate (Spec.Ffdh.primeChecks p.bits) tail
                  pure (if pass then some p.candidate else none, rest))
            cases checkWitnesses p.candidate (Spec.Ffdh.primeChecks p.bits) tail with
            | none => rfl
            | some pair => obtain ⟨pass, tail⟩ := pair; cases pass <;> rfl
      · have nq : Spec.Ffdh.primeShape ((p.candidate - 1) / 2) = false := Bool.eq_false_iff.mpr qp
        simp [gen, pp, nq, candidateAsSpec, candidateRejected]
    · have np : Spec.Ffdh.primeShape p.candidate = false := Bool.eq_false_iff.mpr pp
      simp [gen, np, candidateAsSpec, candidateRejected]
  · have ng : Spec.Ffdh.generationShape p.bits p.generator p.candidate = false := Bool.eq_false_iff.mpr gen
    simp [ng, candidateAsSpec, candidateRejected]

def candidateAnswer (p : CandidateParams) : Option (Bool × List Byte) :=
  if p.length ≤ p.bytes.length then candidateScreen p else none

theorem candidateAnswer_spec (p : CandidateParams) :
    candidateAsSpec p (candidateAnswer p) = Spec.Ffdh.parameterCandidate p.bits p.generator p.bytes := by
  by_cases enough : p.length ≤ p.bytes.length
  · rw [candidateAnswer, ite_eq_left enough]
    exact candidateScreen_spec p enough
  · rw [candidateAnswer, ite_eq_right enough, ← checkedCandidate_eq]
    unfold checkedCandidate
    have short : p.bytes.length < (p.bits + 7) / 8 := by change p.bytes.length < p.length; omega
    rw [draw_of_short short]
    rfl

end VG.Proof.Ffdh.Arm.ParameterCandidate
