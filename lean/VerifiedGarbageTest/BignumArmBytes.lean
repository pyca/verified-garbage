import VerifiedGarbage.Proof.Bignum.Arm.LoadBEFnCT
import VerifiedGarbage.Proof.Bignum.Arm.CopyRegion
import VerifiedGarbage.Proof.Bignum.Arm.CopyBytesCT
import VerifiedGarbage.Proof.Bignum.Arm.LoadBE
import VerifiedGarbage.Proof.Bignum.Arm.LoadBECT
import VerifiedGarbage.Proof.Bignum.Arm.StoreBE
import VerifiedGarbage.Proof.Bignum.Arm.ReverseBytesCT
import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.TCB.Audit

/-! Audit runtime-sized ARMv7 endian conversion. -/

#assert_standard_axioms VG.Proof.Bignum.Arm.ReverseInv.os2ip
#assert_standard_axioms VG.Proof.Bignum.Arm.reverseBytes_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.reverseBytes_ct
#assert_standard_axioms VG.Proof.Bignum.Arm.reverseCtx_of_regions
#assert_standard_axioms VG.Proof.Bignum.Arm.ReverseInv.frame
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.reverseBytes

#assert_standard_axioms VG.Proof.Bignum.Arm.loadBE_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.loadBE_ct
#assert_standard_axioms VG.Proof.Bignum.Arm.ReverseInv.i2osp
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.loadBE

#assert_standard_axioms VG.Proof.Bignum.Arm.copyBytes_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.CopyInv.read
#assert_standard_axioms VG.Proof.Bignum.Arm.copyBytes_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.copyBytes

#assert_standard_axioms VG.Proof.Bignum.Arm.loadBEFn_ok
#assert_standard_axioms VG.Proof.Bignum.Arm.loadBEFn_ct
#assert_no_compiler_overrides VG.Impl.Bignum.Arm.loadBEFn
