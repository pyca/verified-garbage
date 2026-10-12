import VerifiedGarbage.Proof.Dsa.X86_64.SigningCT
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyingCT
import VerifiedGarbage.Proof.Dsa.X86_64.InitializedFields
import VerifiedGarbage.Proof.Dsa.X86_64.ShapeSpec
import VerifiedGarbage.Proof.Dsa.X86_64.SignBody
import VerifiedGarbage.Proof.Dsa.X86_64.SignBytesSpec
import VerifiedGarbage.Proof.Dsa.X86_64.SignReleaseCT
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyBody
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyBytesSpec
import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceBridge
import VerifiedGarbage.Proof.Dsa.X86_64.CTBlocks
import VerifiedGarbage.Proof.Dsa.X86_64.CallAddCT
import VerifiedGarbage.Proof.Dsa.X86_64.CallReduceCT
import VerifiedGarbage.Proof.Dsa.X86_64.ChildCT
import VerifiedGarbage.Proof.Dsa.X86_64.ComputeCT
import VerifiedGarbage.Proof.Dsa.X86_64.CoreSignCT
import VerifiedGarbage.Proof.Dsa.X86_64.CoreVerifyCT
import VerifiedGarbage.Proof.Dsa.X86_64.DomainShapeCT
import VerifiedGarbage.Proof.Dsa.X86_64.LastByteCT
import VerifiedGarbage.Proof.Dsa.X86_64.LoadCheckCT
import VerifiedGarbage.Proof.Dsa.X86_64.MinusCT
import VerifiedGarbage.Proof.Dsa.X86_64.OneScanCT
import VerifiedGarbage.Proof.Dsa.X86_64.PrivateKeyCT
import VerifiedGarbage.Proof.Dsa.X86_64.PublicKeyCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyByteChecksCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyMinusCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyRangeCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReadyReduceCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleAddCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCTState
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleCheckCT
import VerifiedGarbage.Proof.Dsa.X86_64.ScheduleReduceCT
import VerifiedGarbage.Proof.Dsa.X86_64.ShapeCTState
import VerifiedGarbage.Proof.Dsa.X86_64.ShapeSizesCT
import VerifiedGarbage.Proof.Dsa.X86_64.ShapeTailCT
import VerifiedGarbage.Proof.Dsa.X86_64.WidthChoiceCT
import VerifiedGarbage.Proof.Dsa.X86_64.WorkspacesCT
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
import VerifiedGarbage.Proof.Dsa.X86_64.AddCT
import VerifiedGarbage.Proof.Dsa.X86_64.AddCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.CallFinishCT
import VerifiedGarbage.Proof.Dsa.X86_64.CallHeadCT
import VerifiedGarbage.Proof.Dsa.X86_64.EntryCT
import VerifiedGarbage.Proof.Dsa.X86_64.EntryFields
import VerifiedGarbage.Proof.Dsa.X86_64.EntryFieldsFrame
import VerifiedGarbage.Proof.Dsa.X86_64.EntryScratch
import VerifiedGarbage.Proof.Dsa.X86_64.FinishCT
import VerifiedGarbage.Proof.Dsa.X86_64.PowerCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.ProductCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceByteCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCallCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceInitCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceLoopCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceReadCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetupCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceStepCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReleaseBytes
import VerifiedGarbage.Proof.Dsa.X86_64.ScanFieldCT
import VerifiedGarbage.Proof.Dsa.X86_64.SignCompute
import VerifiedGarbage.Proof.Dsa.X86_64.SignEntry
import VerifiedGarbage.Proof.Dsa.X86_64.SignRelease
import VerifiedGarbage.Proof.Dsa.X86_64.StoreCT
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyCompute
import VerifiedGarbage.Proof.Dsa.X86_64.VerifyEntry
import VerifiedGarbage.Proof.Dsa.X86_64.WorkspaceReady
import VerifiedGarbage.Proof.Dsa.X86_64.WriteSignature
import VerifiedGarbage.Proof.Dsa.X86_64.CoreSign
import VerifiedGarbage.Proof.Dsa.X86_64.CoreVerify
import VerifiedGarbage.Proof.Dsa.X86_64.PublicKey
import VerifiedGarbage.Proof.Dsa.X86_64.PrivateKey
import VerifiedGarbage.Proof.Dsa.X86_64.SignificantCT
import VerifiedGarbage.Proof.Dsa.X86_64.ChildBases
import VerifiedGarbage.Proof.Dsa.X86_64.ChildCount
import VerifiedGarbage.Proof.Dsa.X86_64.KeyPointers
import VerifiedGarbage.Proof.Dsa.X86_64.InitInverseCT
import VerifiedGarbage.Proof.Dsa.X86_64.WriteScalar
import VerifiedGarbage.Proof.Dsa.X86_64.WriteScalarCT
import VerifiedGarbage.Proof.Dsa.X86_64.Parent
import VerifiedGarbage.Proof.Dsa.X86_64.Result
import VerifiedGarbage.Proof.Dsa.X86_64.BoundaryCT
import VerifiedGarbage.Proof.Dsa.X86_64.FailureCT
import VerifiedGarbage.Proof.Dsa.X86_64.DomainShape
import VerifiedGarbage.Proof.Dsa.X86_64.ModulusMinus
import VerifiedGarbage.Proof.Dsa.X86_64.IsOne
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

#assert_standard_axioms VG.Proof.Dsa.X86_64.checkCall_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.oneScan_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.loadOne_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.isOne_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.minusCore_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.minus_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.resultCall_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.modulusMinus_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.widthChoice_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.scanField_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.shapeP_context

#assert_standard_axioms VG.Proof.Dsa.X86_64.shapeQ_context

#assert_standard_axioms VG.Proof.Dsa.X86_64.shapeSizes_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.oddCheck_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.shapeFinish_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.shapeTail_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.shapeValid_spec

#assert_standard_axioms VG.Proof.Dsa.X86_64.domainShape_ok

#assert_standard_axioms VG.Proof.Dsa.supported_scans
#assert_standard_axioms VG.Proof.Dsa.subgroup_scan_width
#assert_standard_axioms VG.Proof.Dsa.decodeBE_last_mod_two

#assert_standard_axioms VG.Proof.Dsa.X86_64.parent_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.result_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.parent_ct

#assert_standard_axioms VG.Proof.Dsa.X86_64.result_ct

#assert_standard_axioms VG.Proof.Dsa.X86_64.signFailure_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.signFailure_ct

#assert_standard_axioms VG.Proof.Dsa.X86_64.copyMasked_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.scalarHead_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.writeScalar_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.writeR_ct

#assert_standard_axioms VG.Proof.Dsa.X86_64.writeS_ct

#assert_standard_axioms VG.Proof.Dsa.X86_64.save_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.save_ct

#assert_standard_axioms VG.Proof.Dsa.X86_64.keyPointers_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.keyPointerMem_fields

#assert_standard_axioms VG.Proof.Dsa.X86_64.keyPointerMem_frame

#assert_standard_axioms VG.Proof.Dsa.X86_64.initInverse_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.initInverse_ct

#assert_standard_axioms VG.Proof.Dsa.X86_64.childBases_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.childCount_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.newChild_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.sealChild_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.child_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.workspaces_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.significantChoose_ct

#assert_standard_axioms VG.Proof.Dsa.X86_64.significantByte_ct

#assert_standard_axioms VG.Proof.Dsa.X86_64.significantLoop_ct

#assert_standard_axioms VG.Proof.Dsa.X86_64.significant_ct

#assert_standard_axioms VG.Proof.Dsa.X86_64.readyPow_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.readyProduct_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.readyReduce_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.readyAdd_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.coreSign_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.coreVerify_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.readyRange_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.readyIsOne_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.readyZero_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.readyEqual_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.readyMinus_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.publicKey_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.privateKey_ok

#assert_standard_axioms VG.Proof.Dsa.encodeBE_length
#assert_standard_axioms VG.Proof.Dsa.decodeBE_encodeBE
#assert_standard_axioms VG.Proof.Dsa.encodeBE_decodeBE
#assert_standard_axioms VG.Proof.Dsa.decodeBE_lt
#assert_standard_axioms VG.Proof.Dsa.encodeBE_eq_bytes
#assert_standard_axioms VG.Proof.Dsa.bytesAt_slice
#assert_standard_axioms VG.Proof.Dsa.publicKeyBytes_at
#assert_standard_axioms VG.Proof.Dsa.privateKeyBytes_at
#assert_standard_axioms VG.Proof.Dsa.bitLength_mono
#assert_standard_axioms VG.Proof.Dsa.supported_bounds
#assert_standard_axioms VG.Proof.Dsa.X86_64.publicAccepted_spec
#assert_standard_axioms VG.Proof.Dsa.X86_64.privateAccepted_spec
#assert_standard_axioms VG.Proof.Dsa.X86_64.signAccepted_nonzero
#assert_standard_axioms VG.Proof.Dsa.X86_64.verifyAccepted_value
#assert_standard_axioms VG.Proof.Dsa.X86_64.addCode_eq
#assert_standard_axioms VG.Proof.Dsa.X86_64.addHead_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.addCarry_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.pins_addHead
#assert_standard_axioms VG.Proof.Dsa.X86_64.pins_addMid
#assert_standard_axioms VG.Proof.Dsa.X86_64.addCode_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.callLoad_context
#assert_standard_axioms VG.Proof.Dsa.X86_64.addCall_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.FinishPre.work
#assert_standard_axioms VG.Proof.Dsa.X86_64.powerFinish_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.productFinish_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.reduceFinish_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.sourceBytes_eq
#assert_standard_axioms VG.Proof.Dsa.X86_64.addFinish_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.callHead_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.callHead_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.corePow_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.pins_entryPtrs
#assert_standard_axioms VG.Proof.Dsa.X86_64.entryScratch_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.signEntry_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.verifyEntry_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.field_write_stack
#assert_standard_axioms VG.Proof.Dsa.X86_64.signFields_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.verifyFields_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.field_write_frame
#assert_standard_axioms VG.Proof.Dsa.X86_64.signFieldMem_fields
#assert_standard_axioms VG.Proof.Dsa.X86_64.verifyFieldMem_fields
#assert_standard_axioms VG.Proof.Dsa.X86_64.signFieldMem_frame
#assert_standard_axioms VG.Proof.Dsa.X86_64.verifyFieldMem_frame
#assert_standard_axioms VG.Proof.Dsa.X86_64.stackAddress
#assert_standard_axioms VG.Proof.Dsa.X86_64.entryScratch_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.saved_ne_r11
#assert_standard_axioms VG.Proof.Dsa.X86_64.entry_stack_frame
#assert_standard_axioms VG.Proof.Dsa.X86_64.entry_saved_frame
#assert_standard_axioms VG.Proof.Dsa.X86_64.finish_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.PowerCallBytes.frame
#assert_standard_axioms VG.Proof.Dsa.X86_64.powerCall_prepare
#assert_standard_axioms VG.Proof.Dsa.X86_64.powerCall_load
#assert_standard_axioms VG.Proof.Dsa.X86_64.powerCall_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.productCall_load
#assert_standard_axioms VG.Proof.Dsa.X86_64.productCall_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.reduceRead_arithmetic
#assert_standard_axioms VG.Proof.Dsa.X86_64.reduceArithmetic_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.reduceByte_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.reduceCall_setup
#assert_standard_axioms VG.Proof.Dsa.X86_64.reduceCall_init
#assert_standard_axioms VG.Proof.Dsa.X86_64.reduceCall_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.reduceInit_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.reduceLoop_step
#assert_standard_axioms VG.Proof.Dsa.X86_64.reduceLoop_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.reduceRead_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.reduceSetup_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.reduceStep_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.bytesAt_split
#assert_standard_axioms VG.Proof.Dsa.X86_64.bytesAt_masked
#assert_standard_axioms VG.Proof.Dsa.X86_64.scanField_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.signCompute_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.signEntry_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.signRelease_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.store_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.verifyCompute_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.verifyEntry_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.workspace_field
#assert_standard_axioms VG.Proof.Dsa.X86_64.workspace_outside
#assert_standard_axioms VG.Proof.Dsa.X86_64.workspacesReady_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.writeSignature_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.splitBlock_exec
#assert_standard_axioms VG.Proof.Dsa.X86_64.fuseBlocks_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.callAddHead_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.coreAdd_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.reduceHead_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.coreReduce_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.childHead_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.loadModulus_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.sealChild_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.child_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.signComputeInputs_stable
#assert_standard_axioms VG.Proof.Dsa.X86_64.verifyComputeInputs_stable
#assert_standard_axioms VG.Proof.Dsa.X86_64.signCompute_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.verifyCompute_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.signInputs_stable
#assert_standard_axioms VG.Proof.Dsa.X86_64.coreSignSchedule_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.coreSign_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.verifyInputs_stable
#assert_standard_axioms VG.Proof.Dsa.X86_64.coreVerifySchedule_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.coreVerify_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.domainShape_split
#assert_standard_axioms VG.Proof.Dsa.X86_64.domainShape_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.lastByte_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.oddCheck_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.loadCheck_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.loadedRange_trace
#assert_standard_axioms VG.Proof.Dsa.X86_64.loadedRange_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.leaveAccumulate_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.pins_minusRegs
#assert_standard_axioms VG.Proof.Dsa.X86_64.minusHead_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.minusCore_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.minusFinish_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.pins_oneRegs
#assert_standard_axioms VG.Proof.Dsa.X86_64.oneScanHead_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.oneScan_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.oneReturn_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.privateKey_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.publicKey_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.readyZero_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.readyEqual_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.Ready.publicPointer
#assert_standard_axioms VG.Proof.Dsa.X86_64.readyCall_pre
#assert_standard_axioms VG.Proof.Dsa.X86_64.readyPow_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.readyProduct_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.readyAdd_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.minusCallHead_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.readyMinus_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.checkHead_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.readyRange_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.readyIsOne_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.readyReduce_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.scheduleScalarAdd_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.ExternalAvailable.active
#assert_standard_axioms VG.Proof.Dsa.X86_64.Ready.availableLocal
#assert_standard_axioms VG.Proof.Dsa.X86_64.CallResult.schedule
#assert_standard_axioms VG.Proof.Dsa.X86_64.CallResult.reduced
#assert_standard_axioms VG.Proof.Dsa.X86_64.SchedulePublic.greater
#assert_standard_axioms VG.Proof.Dsa.X86_64.SchedulePublic.odd
#assert_standard_axioms VG.Proof.Dsa.X86_64.SchedulePublic.fits
#assert_standard_axioms VG.Proof.Dsa.X86_64.scalar_space
#assert_standard_axioms VG.Proof.Dsa.X86_64.element_space
#assert_standard_axioms VG.Proof.Dsa.X86_64.schedulePow_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.scheduleProduct_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.CheckEffect.schedule
#assert_standard_axioms VG.Proof.Dsa.X86_64.scheduleRange_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.scheduleIsOne_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.scheduleZero_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.scheduleEqual_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.scheduleMinus_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.scheduleReduce_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.CallResult.keepReduced
#assert_standard_axioms VG.Proof.Dsa.X86_64.scheduleReduceKeep_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.ShapeContext.frame
#assert_standard_axioms VG.Proof.Dsa.X86_64.ShapeContext.sameMem
#assert_standard_axioms VG.Proof.Dsa.X86_64.shapeScan_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.shapeP_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.shapeQScan_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.shapeQ_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.shapeWidth_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.shapeSizes_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.shapeAccumulate_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.shapeOdd_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.shapeTail_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.widthChoice_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.ShapeContext.preserve
#assert_standard_axioms VG.Proof.Dsa.X86_64.workspaceParent_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.workspaceChild_pre
#assert_standard_axioms VG.Proof.Dsa.X86_64.workspaceChild_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.workspaces_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.signFieldMem_unused
#assert_standard_axioms VG.Proof.Dsa.X86_64.verifyFieldMem_unused
#assert_standard_axioms VG.Proof.Dsa.X86_64.callHead_run
#assert_standard_axioms VG.Proof.Dsa.X86_64.coreProduct_ct

#assert_standard_axioms VG.Proof.Dsa.X86_64.SignEntryPost.shapeFields
#assert_standard_axioms VG.Proof.Dsa.X86_64.VerifyEntryPost.shapeFields
#assert_standard_axioms VG.Proof.Dsa.X86_64.decodeBE_last_parity
#assert_standard_axioms VG.Proof.Dsa.X86_64.shapeAccepted_spec
#assert_standard_axioms VG.Proof.Dsa.X86_64.shapeAccepted_false
#assert_standard_axioms VG.Proof.Dsa.X86_64.signBytes_invalid_shape
#assert_standard_axioms VG.Proof.Dsa.X86_64.verifyBytes_invalid_shape
#assert_standard_axioms VG.Proof.Dsa.X86_64.signBody_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.signBody_spec
#assert_standard_axioms VG.Proof.Dsa.X86_64.signNonce_compute
#assert_standard_axioms VG.Proof.Dsa.X86_64.signBytes_compute
#assert_standard_axioms VG.Proof.Dsa.X86_64.releaseScalar_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.signRelease_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.verifyBody_ok
#assert_standard_axioms VG.Proof.Dsa.X86_64.verifyBody_spec
#assert_standard_axioms VG.Proof.Dsa.X86_64.verifyValue_compute
#assert_standard_axioms VG.Proof.Dsa.X86_64.verifyBytes_compute
#assert_standard_axioms VG.Proof.Dsa.X86_64.ChildReady.inverse_unique
#assert_standard_axioms VG.Proof.Dsa.X86_64.readyInverses_eq
#assert_standard_axioms VG.Proof.Dsa.X86_64.initialization_ct
#assert_standard_axioms VG.Proof.Dsa.X86_64.initialization_related

#assert_standard_axioms VG.Proof.Dsa.X86_64.signingMain_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.verifyingMain_ok

#assert_standard_axioms VG.Proof.Dsa.X86_64.signingMain_ct

#assert_standard_axioms VG.Proof.Dsa.X86_64.verifyingMain_ct

#assert_standard_axioms VG.Proof.Dsa.X86_64.signBody_ct

#assert_standard_axioms VG.Proof.Dsa.X86_64.verifyBody_ct
