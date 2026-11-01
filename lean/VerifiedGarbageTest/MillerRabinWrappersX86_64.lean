module

import VerifiedGarbage.Proof.MillerRabin.X86_64.Context
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Context
import VerifiedGarbage.Proof.MillerRabin.X86_64.Frame
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Frame
import VerifiedGarbage.Proof.MillerRabin.X86_64.Stage
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Stage
import VerifiedGarbage.Proof.MillerRabin.X86_64.Normalize
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Normalize
import VerifiedGarbage.Proof.MillerRabin.X86_64.FramedBody
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.FramedBody
import VerifiedGarbage.Proof.MillerRabin.X86_64.EntrySaved
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.EntrySaved
import VerifiedGarbage.Proof.MillerRabin.X86_64.StackCall
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.StackCall
import VerifiedGarbage.Proof.MillerRabin.X86_64.StackPrepared
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.StackPrepared
import VerifiedGarbage.Proof.MillerRabin.X86_64.StageContext
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.StageContext
import VerifiedGarbage.Proof.MillerRabin.X86_64.Correct
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Correct
import VerifiedGarbage.Proof.MillerRabin.X86_64.FramedCall
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.FramedCall
import VerifiedGarbage.Proof.MillerRabin.X86_64.BodyCT
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.BodyCT
import VerifiedGarbage.Proof.MillerRabin.X86_64.StackRegions
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.StackRegions
import VerifiedGarbage.Proof.MillerRabin.X86_64.Verified
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Verified
import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerCT
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerCT
import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedVerified
meta import VerifiedGarbage.Proof.RsaKeyGen.X86_64.SharedVerified
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Proof.MillerRabin.X86_64.BodyKeeps
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.BodyKeeps
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerResult
meta import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerResult

/-! Audit wrapper lemmas before the callable artifacts are registered. -/

#assert_standard_axioms VG.Proof.MillerRabin.X86_64.core_keeps
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.stage_ok
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.normalize_ok

#assert_standard_axioms VG.Proof.MillerRabin.X86_64.initial_ctx
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.round_implies
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.normalized_header

#assert_standard_axioms VG.Proof.MillerRabin.X86_64.body_keeps_ok
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.framed_body_ok
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.entered_saved_headers
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.entered_clear
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.entered_ctx
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.entered_exp
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.staged_context

#assert_standard_axioms VG.Proof.MillerRabin.X86_64.round_correct
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.framed_call_ok
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.body_ct
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.entered_kw

#assert_standard_axioms VG.Proof.MillerRabin.X86_64.round_verified

#assert_standard_axioms VG.Proof.MillerRabin.X86_64.Caller.call_result_ok
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.Caller.call_ct
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.Kernel.called

#assert_standard_axioms VG.Proof.RsaKeyGen.X86_64.sharedCandidate_verified
