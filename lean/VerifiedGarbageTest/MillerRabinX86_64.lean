module

import VerifiedGarbage.Proof.MillerRabin.X86_64.Core
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Core
import VerifiedGarbage.Proof.MillerRabin.X86_64.CT
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CT
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms

/-! Audit the shared round's x86-64 core proofs before their callable artifacts land. -/

#assert_standard_axioms VG.Proof.MillerRabin.X86_64.core_ok
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.core_ct
