import VerifiedGarbage.Proof.Dsa.X86_64
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! # Trust audits for the DSA implementation's arithmetic groundwork

These are dependency audits, not assertions of complete sign/verify support.
The whole-operation contracts must be proved before artifacts are registered.
-/

#assert_standard_axioms VG.Proof.Dsa.X86_64.mulLo_verified
#assert_standard_axioms VG.Proof.Dsa.X86_64.mulHi_verified
#assert_standard_axioms VG.Proof.Dsa.X86_64.select_verified
#assert_standard_axioms VG.Proof.Dsa.powMod_rsa
#assert_standard_axioms VG.Proof.Dsa.powMod_eq
#assert_standard_axioms VG.Proof.Dsa.reduceBytes_eq
#assert_standard_axioms VG.Proof.Dsa.sign_residues
#assert_standard_axioms VG.Proof.Dsa.verify_residues
#assert_standard_axioms VG.Proof.Dsa.mont_scale
#assert_standard_axioms VG.Proof.Dsa.X86_64.reduceStep_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.scratchSource
#assert_standard_axioms VG.Proof.Dsa.X86_64.expLoop_ok
