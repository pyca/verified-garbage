import VerifiedGarbage.Proof.Dsa.X86_64.ZeroCT
import VerifiedGarbage.Proof.Dsa.X86_64.Zero
import VerifiedGarbage.Proof.Dsa.X86_64.Equal
import VerifiedGarbage.Proof.Dsa.X86_64.EqualCT
import VerifiedGarbage.Proof.Dsa.Zero
import VerifiedGarbage.Proof.Dsa.X86_64.Range
import VerifiedGarbage.Proof.Dsa.X86_64.RangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.WidthMask
import VerifiedGarbage.Proof.Dsa.X86_64.CoreCalls
import VerifiedGarbage.Proof.Dsa.X86_64.CoreReduce
import VerifiedGarbage.Proof.Dsa.X86_64.CoreAdd
import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify
import VerifiedGarbage.Proof.Dsa.Layout
import VerifiedGarbage.Proof.Dsa.DomainShape
import VerifiedGarbage.Proof.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.X86_64.SetupCT
import VerifiedGarbage.Proof.Dsa.X86_64.Multiply
import VerifiedGarbage.Proof.Dsa.X86_64.Reduce
import VerifiedGarbage.Proof.Dsa.X86_64.ProductCT
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Dsa.X86_64.Store
import VerifiedGarbage.Proof.Dsa.X86_64.CallHeader
import VerifiedGarbage.Proof.Dsa.X86_64.Finish
import VerifiedGarbage.Proof.Dsa.X86_64.SignificantLoop
import VerifiedGarbage.Proof.Dsa.X86_64.Power
import VerifiedGarbage.Proof.Dsa.X86_64.PowerCT
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

#assert_standard_axioms VG.Proof.Dsa.workspace_bounds
#assert_standard_axioms VG.Proof.Dsa.scalar_buffer_bounds
#assert_standard_axioms VG.Proof.Dsa.digestScalar_prefix
#assert_standard_axioms VG.Proof.Dsa.encodeBE_i2osp
#assert_standard_axioms VG.Proof.Dsa.signWithNonce_reduced
#assert_standard_axioms VG.Proof.Dsa.verify_reduced
#assert_standard_axioms VG.Proof.Dsa.X86_64.constants_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.productCore_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.productCore_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.load_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.store_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.encodePower_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.powerCore_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.encodePower_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.exponent_ct

#assert_standard_axioms VG.Proof.Dsa.X86_64.prepare_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.load_mod_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.power_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.product_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.constants_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.encodedPower_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.powerCore_ct

#assert_standard_axioms VG.Proof.Dsa.X86_64.reduceSetup_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.reduce_ok

#assert_standard_axioms VG.Proof.Dsa.significant_width

#assert_standard_axioms VG.Proof.Dsa.X86_64.significant_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.operand_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.enter_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.leave_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.operand_context
#assert_standard_axioms VG.Proof.Dsa.X86_64.storeSuffix_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.finish_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.returnAfter_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.call_ready

#assert_standard_axioms VG.Proof.Dsa.X86_64.arguments_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.arguments2_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.call3_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.call2_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.corePow_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.coreProduct_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.coreReduce_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.add_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.coreAdd_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.orWords_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.rangeLow_words
#assert_standard_axioms VG.Proof.Dsa.X86_64.rangeMask_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.rangeMask_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.accumulate_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.widthMask_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.loadRange_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.accumulate_context
#assert_standard_axioms VG.Proof.Dsa.X86_64.range_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.zeroLoop_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.zeroMask_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.zero_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.equalLoop_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.equal_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.equal_ct
#assert_standard_axioms VG.Proof.Dsa.decodeBE_eq_zero

#assert_standard_axioms VG.Proof.Dsa.X86_64.zero_ct
