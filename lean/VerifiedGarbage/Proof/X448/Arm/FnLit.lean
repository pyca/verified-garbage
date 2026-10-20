module

public import VerifiedGarbage.Impl.X448.Arm
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.X448.Arm
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Arm.Lit
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-!
# X448 on ARMv7: the field functions as literals

The callers' literals refer to these (`materialize_code`), so the kernel
builds each function's code once.
-/

@[expose] public section

namespace VG

materialize_code Impl.X448.Arm.mulFn
materialize_code Impl.X448.Arm.addFn
materialize_code Impl.X448.Arm.subFn
materialize_code Impl.X448.Arm.mulA24Fn

end VG
