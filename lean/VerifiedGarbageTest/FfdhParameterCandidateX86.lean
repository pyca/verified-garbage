module

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Shape
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Shape
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Halve
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Halve
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Sieve
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Residue
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Residue
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ChecksCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ChecksCT
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Load
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Load
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Prepared
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.WordShape
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.WordShape
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeCT
meta import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.ShapeCT
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve
meta import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.Sieve

/-! Audit the exact byte encodings, native candidate shaping, and in-place halving. -/

#assert_standard_axioms VG.Proof.Ffdh.ParameterCandidate.shapedOctets_value
#assert_standard_axioms VG.Proof.Ffdh.ParameterCandidate.shapedOctets_half_value
#assert_standard_axioms VG.Proof.Ffdh.X86_64.ParameterCandidate.shape_ok
#assert_standard_axioms VG.Proof.Ffdh.X86_64.ParameterCandidate.halve_ok
#assert_standard_axioms VG.Proof.Ffdh.ParameterCandidate.sieve_entries
#assert_standard_axioms VG.Proof.Ffdh.ParameterCandidate.primeShape_sieve
#assert_standard_axioms VG.Proof.Ffdh.X86_64.ParameterCandidate.primeCheck_ok
#assert_standard_axioms VG.Proof.Ffdh.X86_64.ParameterCandidate.generatorCheck_ok
#assert_standard_axioms VG.Proof.Ffdh.X86_64.ParameterCandidate.sieve_ct
#assert_standard_axioms VG.Proof.Ffdh.X86_64.ParameterCandidate.generatorCheck_ct
#assert_standard_axioms VG.Proof.Ffdh.ParameterCandidate.half_word_shape
#assert_standard_axioms VG.Proof.Ffdh.ParameterCandidate.candidate_load_widths
#assert_standard_axioms VG.Proof.Ffdh.X86_64.ParameterCandidate.loadCandidate_ok
#assert_standard_axioms VG.Proof.Ffdh.X86_64.ParameterCandidate.prepareModulus_ok
#assert_standard_axioms VG.Proof.Ffdh.X86_64.ParameterCandidate.shape_ct
#assert_standard_axioms VG.Proof.Ffdh.X86_64.ParameterCandidate.halve_ct
