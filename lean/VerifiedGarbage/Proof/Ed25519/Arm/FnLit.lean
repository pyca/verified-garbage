import VerifiedGarbage.Impl.Ed25519.Arm.Power
import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! The functions of point arithmetic and the inversion chain, and their
bodies, as literals (`materialize_code`), which their own constant-time
checks and the literals of the code that calls them read rather than build
each field multiplication again. -/
namespace VG.Impl.Ed25519.Arm

materialize_code pointAdd
materialize_code pointDouble
materialize_code chain250
materialize_code Point16.addFn
materialize_code Point16.doubleFn
materialize_code pow250Fn

end VG.Impl.Ed25519.Arm
