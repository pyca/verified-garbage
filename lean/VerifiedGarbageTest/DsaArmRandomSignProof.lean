module

import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignVerified
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignVerified
import VerifiedGarbage.Proof.Dsa.AArch64.RandomPrepareCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomPrepareCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSampleCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSampleCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRetryCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignRetryCT
import VerifiedGarbage.Proof.Dsa.RandomTraceResult
meta import VerifiedGarbage.Proof.Dsa.RandomTraceResult
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSingleCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSingleCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSampleCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignSampleCT
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignInitCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignInitCT
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCode
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCode
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignConstantTime
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignConstantTime
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCorrect
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCorrect
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinishResult
meta import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignFinishResult
import VerifiedGarbage.Proof.Dsa.RandomSignTrace
meta import VerifiedGarbage.Proof.Dsa.RandomSignTrace

/-! Audit the complete functional-correctness chain independently of model execution. -/
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_sign_correct
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_sign_sp
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_sign_depth
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_sign_code
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_sign_loop_correct

#assert_standard_axioms VG.Proof.Dsa.AArch64.random_prepare_ct
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_sample_ct
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_draw_ct

#assert_standard_axioms VG.Proof.Dsa.AArch64.random_signer_ct
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_callFinish_ct
#assert_standard_axioms VG.Proof.Dsa.random_sign_trace_draw
#assert_standard_axioms VG.Proof.Dsa.Random.sample_trace_agree

#assert_standard_axioms VG.Proof.Dsa.AArch64.random_sign_single_agreement
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_sign_sample_agreement
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_sign_init_ct

#assert_standard_axioms VG.Proof.Dsa.AArch64.random_sign_verified
#assert_standard_axioms VG.Proof.Dsa.AArch64.random_sign_constantTime
