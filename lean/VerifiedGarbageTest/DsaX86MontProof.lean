import VerifiedGarbage.Proof.Mont.X86.DynamicOps
import VerifiedGarbage.Proof.Mont.X86.Inverse
import VerifiedGarbage.Proof.Mont.X86.PowerTiming
import VerifiedGarbage.TCB.Axioms

/-! Audit the runtime-modulus arithmetic independently of executable tests. -/
#assert_standard_axioms VG.Proof.Mont.X86.Dynamic.mul_ok
#assert_standard_axioms VG.Proof.Mont.X86.Dynamic.setupInverse_ok
#assert_standard_axioms VG.Proof.Mont.X86.Dynamic.mul_constantTime
