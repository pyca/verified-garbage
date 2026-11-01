module

import VerifiedGarbage.Proof.MillerRabin.AArch64.Verified
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.Verified
import VerifiedGarbage.Proof.MillerRabin.AArch64.Frame
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.Frame
import VerifiedGarbage.Proof.MillerRabin.AArch64.Finish
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.Finish
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedVerified
meta import VerifiedGarbage.Proof.RsaKeyGen.AArch64.SharedVerified
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerResult
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerResult
import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerCT
meta import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerCT
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.TCB.Axioms

/-! Audit wrapper lemmas before the callable artifacts are registered. -/

#assert_standard_axioms VG.Proof.MillerRabin.AArch64.core_keeps
#assert_standard_axioms VG.Proof.MillerRabin.AArch64.returnFlag_ok

#assert_standard_axioms VG.Proof.MillerRabin.AArch64.round_verified

#assert_standard_axioms VG.Proof.MillerRabin.AArch64.Caller.call_result_ok
#assert_standard_axioms VG.Proof.MillerRabin.AArch64.Caller.call_ct

#assert_standard_axioms VG.Proof.RsaKeyGen.AArch64.sharedCandidate_verified
