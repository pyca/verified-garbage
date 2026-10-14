import VerifiedGarbage.Proof.MillerRabin.AArch64.Frame
import VerifiedGarbage.Proof.MillerRabin.AArch64.Finish
import VerifiedGarbage.Proof.MillerRabin.X86_64.Frame
import VerifiedGarbage.Proof.MillerRabin.X86_64.Stage
import VerifiedGarbage.Proof.MillerRabin.X86_64.Normalize
import VerifiedGarbage.TCB.Axioms

/-! Audit wrapper lemmas before the callable artifacts are registered. -/

#assert_standard_axioms VG.Proof.MillerRabin.AArch64.core_keeps
#assert_standard_axioms VG.Proof.MillerRabin.AArch64.returnFlag_ok
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.core_keeps
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.stage_ok
#assert_standard_axioms VG.Proof.MillerRabin.X86_64.normalize_ok
