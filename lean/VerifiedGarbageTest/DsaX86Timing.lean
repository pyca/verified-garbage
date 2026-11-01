module

import VerifiedGarbage.Proof.Dsa.X86.CallPowerTiming
meta import VerifiedGarbage.Proof.Dsa.X86.CallPowerTiming
import VerifiedGarbage.Proof.Dsa.X86.CoreProductTiming
meta import VerifiedGarbage.Proof.Dsa.X86.CoreProductTiming
import VerifiedGarbage.Proof.Dsa.X86.CoreReduceTiming
meta import VerifiedGarbage.Proof.Dsa.X86.CoreReduceTiming
import VerifiedGarbage.Proof.Dsa.X86.ValidationTiming
meta import VerifiedGarbage.Proof.Dsa.X86.ValidationTiming
import VerifiedGarbage.Proof.Dsa.X86.MinusTiming
meta import VerifiedGarbage.Proof.Dsa.X86.MinusTiming
import VerifiedGarbage.Proof.Dsa.X86.BodyTiming
meta import VerifiedGarbage.Proof.Dsa.X86.BodyTiming
import VerifiedGarbage.Proof.Dsa.X86.ShapeTiming
meta import VerifiedGarbage.Proof.Dsa.X86.ShapeTiming
import VerifiedGarbage.Proof.Dsa.X86.DispatchTiming
meta import VerifiedGarbage.Proof.Dsa.X86.DispatchTiming
import VerifiedGarbage.Proof.Dsa.X86.SignSizedTiming
meta import VerifiedGarbage.Proof.Dsa.X86.SignSizedTiming
import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
meta import VerifiedGarbage.Proof.Dsa.X86.EntryTiming
import VerifiedGarbage.Proof.Dsa.X86.Verified
meta import VerifiedGarbage.Proof.Dsa.X86.Verified
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Proof.Dsa.X86.CallMinusTiming
meta import VerifiedGarbage.Proof.Dsa.X86.CallMinusTiming
import VerifiedGarbage.Proof.Dsa.X86.CallProductTiming
meta import VerifiedGarbage.Proof.Dsa.X86.CallProductTiming
import VerifiedGarbage.Proof.Dsa.X86.CallReduceTiming
meta import VerifiedGarbage.Proof.Dsa.X86.CallReduceTiming
import VerifiedGarbage.Proof.Dsa.X86.CallValidationTiming
meta import VerifiedGarbage.Proof.Dsa.X86.CallValidationTiming
import VerifiedGarbage.Proof.Dsa.X86.FailureTiming
meta import VerifiedGarbage.Proof.Dsa.X86.FailureTiming
import VerifiedGarbage.Proof.Dsa.X86.KeyTiming
meta import VerifiedGarbage.Proof.Dsa.X86.KeyTiming
import VerifiedGarbage.Proof.Dsa.X86.SharedTiming
meta import VerifiedGarbage.Proof.Dsa.X86.SharedTiming
import VerifiedGarbage.Proof.Dsa.X86.SignTiming
meta import VerifiedGarbage.Proof.Dsa.X86.SignTiming
import VerifiedGarbage.Proof.Dsa.X86.VerifySizedTiming
meta import VerifiedGarbage.Proof.Dsa.X86.VerifySizedTiming
import VerifiedGarbage.Proof.Dsa.X86.VerifyTiming
meta import VerifiedGarbage.Proof.Dsa.X86.VerifyTiming

/-! Audit the constant-time composition independently of executable tests. -/
#assert_standard_axioms VG.Proof.Dsa.X86.loadComponent_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.storeComponent_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.corePower_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.coreProductMod_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.coreSum_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.coreReduce_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.validateRange_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.validateEqual_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.validateOne_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.validateZero_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.validateMinus_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.callPowerP_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.callPowerQ_relCT

#assert_standard_axioms VG.Proof.Dsa.X86.callProductP_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.callProductQ_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.callReduce_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.callRange_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.callEqual_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.callOne_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.callZero_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.callMinusP_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.callMinusQ_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.callPublicKey_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.callPrivateKey_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.callSignCompute_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.callVerifyCompute_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.writeSignature_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.callSignBody_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.callVerifyBody_relCT

#assert_standard_axioms VG.Proof.Dsa.X86.shape_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.reduceStream_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.widthDispatch_relCT

#assert_standard_axioms VG.Proof.Dsa.X86.signFailure_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.verifyFailure_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.installEntry_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.restore_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.verifySized_relCT
#assert_standard_axioms VG.Proof.Dsa.X86.signSized_relCT

#assert_standard_axioms VG.Proof.Dsa.X86.signingConstantTime
#assert_standard_axioms VG.Proof.Dsa.X86.verifyingConstantTime
#assert_standard_axioms VG.Proof.Dsa.X86.signing_verified
#assert_standard_axioms VG.Proof.Dsa.X86.verifying_verified
