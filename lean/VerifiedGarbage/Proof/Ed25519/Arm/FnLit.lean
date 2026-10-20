module

public import VerifiedGarbage.Impl.Ed25519.Arm.Power
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ed25519.Arm.Power
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! The functions of point arithmetic and the inversion chain, and their
bodies, as literals (`materialize_code`), which their own constant-time
checks and the literals of the code that calls them read rather than build
each field multiplication again. -/

@[expose] public section

namespace VG.Impl.Ed25519.Arm

materialize_code pointAdd
materialize_code pointDouble
materialize_code chain250
materialize_code Point16.addFn
materialize_code Point16.doubleFn
materialize_code pow250Fn

end VG.Impl.Ed25519.Arm
