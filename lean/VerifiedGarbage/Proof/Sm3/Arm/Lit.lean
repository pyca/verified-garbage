import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.Sm3.Arm.Stream

/-!
# SM3 on ARMv7: the code as literals
-/

namespace VG

materialize_code Impl.Sm3.Arm.compress
materialize_code Impl.Sm3.Arm.Stream.update
materialize_code Impl.Sm3.Arm.Stream.finalize

end VG
