import VerifiedGarbage.Proof.Bignum.Arm.InverseReady
import VerifiedGarbage.Proof.Bignum.Arm.InitInverseCT
import VerifiedGarbage.Proof.Bignum.Arm.Minv64
import VerifiedGarbage.Proof.Bignum.Arm.Minv64CT
import VerifiedGarbage.Proof.Bignum.Arm.Mul64CT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit the full 64-bit inverse implemented with ARMv7 register pairs. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.mul64_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.mul64_ct
#assert_standard_axioms VG.Proof.Bignum.Arm.newton64_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.minv64_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.minv64_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.minv64

#assert_standard_axioms VG.Proof.Bignum.Arm.initInverse_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.initInverse_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.initInverse

#assert_standard_axioms VG.Proof.Bignum.Arm.initInverse_ready
