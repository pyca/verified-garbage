module

public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.CandidateTest
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Framework.Omega

/-! # FFDH parameter generation on x86-64: relate the native policy to the specification -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum
open VG.Proof.Ffdh.ParameterCandidate

theorem CandidateBase.candidate_result {p : CandidateP} {s : State} (h : CandidateBase p s)
    (havail : p.k ≤ p.rand.length) :
    Spec.Ffdh.parameterCandidate p.bits p.gen p.rand =
      (candidateTail p (p.rand.drop p.k)).map (fun x => (if x.1 then some p.P else none, x.2)) := by
  rw [← checkedCandidate_eq]
  unfold checkedCandidate
  rw [← h.len, draw_of_le havail]
  simp only [bind, Option.bind_some]
  change (do
    if !(Spec.Ffdh.generationShape p.bits p.gen p.P && Spec.Ffdh.primeShape p.P && Spec.Ffdh.primeShape p.Q) then
      return (none, p.rand.drop p.k)
    let (pass, rest) ← checkWitnesses p.Q (Spec.Ffdh.primeChecks (Spec.RsaKeyGen.bitLength p.Q)) (p.rand.drop p.k)
    if !pass then return (none, rest)
    let (pass, rest) ← checkWitnesses p.P (Spec.Ffdh.primeChecks (Spec.RsaKeyGen.bitLength p.P)) rest
    return (if pass then some p.P else none, rest)) = _
  have hpodd : p.P % 2 = 1 :=
    (candidate_shape (bits := p.bits) (by omega_using [h.bits1]) _).1
  have hpbits : Spec.RsaKeyGen.bitLength p.P = p.phaseBits false := (h.phase_bitLength false hpodd).1
  by_cases hgp : (Spec.Ffdh.generationShape p.bits p.gen p.P && Spec.Ffdh.primeShape p.P) = true
  · by_cases hq : Spec.Ffdh.primeShape p.Q = true
    · have hqodd : p.Q % 2 = 1 := by
        have hh := hq
        unfold Spec.Ffdh.primeShape at hh
        exact beq_iff_eq.mp ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hh).1).2
      have hqbits : Spec.RsaKeyGen.bitLength p.Q = p.phaseBits true := (h.phase_bitLength true hqodd).1
      simp only [hgp, hq, Bool.and_self, Bool.not_true, Bool.false_eq_true, ite_false,
        candidateTail, ite_true, qPolicy, hqbits, hpbits]
      cases he : checkWitnesses p.Q (Spec.Ffdh.primeChecks (p.phaseBits true)) (p.rand.drop p.k) with
      | none => rfl
      | some ar =>
        obtain ⟨pass, rest⟩ := ar
        cases pass
        · rfl
        · simp only [bind, Option.bind_some, Bool.not_true, Bool.false_eq_true, ite_false]
          cases checkWitnesses p.P (Spec.Ffdh.primeChecks (p.phaseBits false)) rest with
          | none => rfl
          | some ar => obtain ⟨pass, rest'⟩ := ar; cases pass <;> rfl
    · have hqf : Spec.Ffdh.primeShape p.Q = false := Bool.eq_false_iff.mpr hq
      simp [candidateTail, qPolicy, hgp, hqf]
  · have hgpf : (Spec.Ffdh.generationShape p.bits p.gen p.P && Spec.Ffdh.primeShape p.P) = false :=
      Bool.eq_false_iff.mpr hgp
    simp [candidateTail, hgpf]

end VG.Proof.Ffdh.X86_64.ParameterCandidate
