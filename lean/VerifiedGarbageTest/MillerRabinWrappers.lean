import VerifiedGarbage.Proof.MillerRabin.AArch64.Verified
import VerifiedGarbage.Proof.MillerRabin.AArch64.Frame
import VerifiedGarbage.Proof.MillerRabin.AArch64.Finish
import VerifiedGarbage.Proof.MillerRabin.X86_64.Context
import VerifiedGarbage.Proof.MillerRabin.X86_64.Frame
import VerifiedGarbage.Proof.MillerRabin.X86_64.Stage
import VerifiedGarbage.Proof.MillerRabin.X86_64.Normalize
import VerifiedGarbage.Proof.MillerRabin.X86_64.FramedBody
import VerifiedGarbage.Proof.MillerRabin.X86_64.EntrySaved
import VerifiedGarbage.Proof.MillerRabin.X86_64.StackCall
import VerifiedGarbage.Proof.MillerRabin.X86_64.StackPrepared
import VerifiedGarbage.Proof.MillerRabin.X86_64.StageContext
import VerifiedGarbage.Proof.MillerRabin.X86_64.Correct
import VerifiedGarbage.Proof.MillerRabin.X86_64.FramedCall
import VerifiedGarbage.Proof.MillerRabin.X86_64.BodyCT
import VerifiedGarbage.Proof.MillerRabin.X86_64.StackRegions
import VerifiedGarbage.TCB.Axioms

/-! Audit wrapper lemmas before the callable artifacts are registered. -/

#assert_standard_axioms VG.Proof.MillerRabin.AArch64.core_keeps
#assert_standard_axioms VG.Proof.MillerRabin.AArch64.returnFlag_ok
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.core_keeps
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.stage_ok
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.normalize_ok

#assert_standard_axioms VG.Proof.MillerRabin.AArch64.round_verified

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
