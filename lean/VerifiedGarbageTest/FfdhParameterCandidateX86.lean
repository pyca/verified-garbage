import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Halve
import VerifiedGarbage.TCB.Axioms

/-! Audit the exact byte encodings, native candidate shaping, and in-place halving. -/

#assert_standard_axioms VG.Proof.Ffdh.ParameterCandidate.shapedOctets_value
#assert_standard_axioms VG.Proof.Ffdh.ParameterCandidate.shapedOctets_half_value
#assert_standard_axioms VG.Proof.Ffdh.X86_64.ParameterCandidate.shape_ok
#assert_standard_axioms VG.Proof.Ffdh.X86_64.ParameterCandidate.halve_ok
