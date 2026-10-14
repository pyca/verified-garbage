import VerifiedGarbage.Proof.MillerRabin.X86_64.Core
import VerifiedGarbage.Proof.MillerRabin.X86_64.CT
import VerifiedGarbage.Proof.MillerRabin.AArch64.Core
import VerifiedGarbage.Proof.MillerRabin.Representation
import VerifiedGarbage.TCB.Axioms

/-! Audit the shared round's core proofs before their callable artifacts land. -/

#assert_standard_axioms VG.Proof.MillerRabin.X86_64.core_ok
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.core_ct
#assert_standard_axioms VG.Proof.MillerRabin.AArch64.core_ok
#assert_standard_axioms VG.Proof.MillerRabin.AArch64.core_ct
#assert_standard_axioms VG.Proof.MillerRabin.round_mod
#assert_standard_axioms VG.Proof.MillerRabin.witness_exists
