import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Proof.Idea.KeyLit32
import VerifiedGarbage.Impl.Idea.Arm

/-! # Literal IDEA programs for kernel-evaluated checks (ARMv7) -/

namespace VG

materialize_code Impl.Idea.Arm.expandKey
materialize_code Impl.Idea.Arm.invertKey
materialize_code Impl.Idea.Arm.ecb

end VG
