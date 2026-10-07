import VerifiedGarbage.Proof.Framework.Arm.Lit
import VerifiedGarbage.Impl.X448.Arm

/-!
# X448 on ARMv7: the field functions as literals

The callers' literals refer to these (`materialize_code`), so the kernel
builds each function's code once.
-/

namespace VG

materialize_code Impl.X448.Arm.mulFn
materialize_code Impl.X448.Arm.addFn
materialize_code Impl.X448.Arm.subFn
materialize_code Impl.X448.Arm.mulA24Fn

end VG
