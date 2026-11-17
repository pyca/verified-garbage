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
each field multiplication again: each with the baseline's multiplication
(`…Plain`) and with `umaal` (`…Umaal`). -/

@[expose] public section

namespace VG.Impl.Ed25519.Arm

materialize_code pointAddPlain := pointAdd false
materialize_code pointAddUmaal := pointAdd true
materialize_code pointDoublePlain := pointDouble false
materialize_code pointDoubleUmaal := pointDouble true
materialize_code chain250Plain := chain250 false
materialize_code chain250Umaal := chain250 true
materialize_code addFnPlain := Point16.addFn false
materialize_code addFnUmaal := Point16.addFn true
materialize_code doubleFnPlain := Point16.doubleFn false
materialize_code doubleFnUmaal := Point16.doubleFn true
materialize_code pow250FnPlain := pow250Fn false
materialize_code pow250FnUmaal := pow250Fn true

end VG.Impl.Ed25519.Arm
