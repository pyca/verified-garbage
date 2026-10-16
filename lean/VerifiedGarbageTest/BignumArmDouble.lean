import VerifiedGarbage.Proof.Bignum.Arm.R2CT
import VerifiedGarbage.Proof.Bignum.Arm.DoubleBody
import VerifiedGarbage.Proof.Bignum.Arm.DoubleFnRestore
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Bignum.Arm.DoubleCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit modular doubling used by ARMv7 RSA key precomputation. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.doubleBody_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.doubleBody_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.doubleBody

#assert_standard_axioms VG.Proof.Bignum.Arm.doubleFnRestore_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.doubleFnRestore_ct
#assert_standard_axioms VG.Proof.Bignum.Arm.keeps_layout
#assert_standard_axioms VG.Proof.Bignum.Arm.keeps_array_num
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.doubleFnRestore

#assert_standard_axioms VG.Proof.Bignum.Arm.doubleLoop_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.r2_from_one
#assert_standard_axioms VG.Proof.Bignum.Arm.doubleLoop_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.doubleLoop

#assert_standard_axioms VG.Proof.Bignum.Arm.r2_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.r2_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.r2
