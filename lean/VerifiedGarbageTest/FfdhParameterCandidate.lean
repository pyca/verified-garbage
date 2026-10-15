import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Domain
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Witness
import VerifiedGarbage.TCB.Axioms

/-! Audit candidate widths, generated domains, and the uniform witness stream. -/

#assert_standard_axioms VG.Proof.Ffdh.ParameterCandidate.candidate_bitLength
#assert_standard_axioms VG.Proof.Ffdh.ParameterCandidate.half_witnessOctets
#assert_standard_axioms VG.Proof.Ffdh.ParameterCandidate.candidate_widths
#assert_standard_axioms VG.Proof.Ffdh.ParameterCandidate.candidate_parametersValid
#assert_standard_axioms VG.Proof.Ffdh.ParameterCandidate.drawWitnesses_probable
