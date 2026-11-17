module

public import VerifiedGarbage.Proof.Ed25519.Arm.FnLit
public import VerifiedGarbage.Impl.Ed25519.Arm.PointAccumulate
public import VerifiedGarbage.Impl.Ed25519.Arm.PointEncode
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Ed25519.Arm.FnLit
meta import VerifiedGarbage.Impl.Ed25519.Arm.PointAccumulate
meta import VerifiedGarbage.Impl.Ed25519.Arm.PointEncode
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Proof.Framework.Arm.Lit

/-! The calls of the point arithmetic and the inversion chain as literals
(`materialize_value`, `materialize_code`), which the literals of the code
that contains them read rather than build each field multiplication again. -/

@[expose] public section

namespace VG.Impl.Ed25519.Arm

materialize_code addCallPlain := Point16.addCall false
materialize_code addCallUmaal := Point16.addCall true
materialize_code doubleCallPlain := Point16.doubleCall false
materialize_code doubleCallUmaal := Point16.doubleCall true
materialize_code power250Plain := power250 false
materialize_code power250Umaal := power250 true
materialize_code invertPlain := invert false
materialize_code invertUmaal := invert true
materialize_code rootPowerPlain := rootPower false
materialize_code rootPowerUmaal := rootPower true

end VG.Impl.Ed25519.Arm

namespace VG.Impl.Ed25519.Arm
materialize_code pointEncodePlain := pointEncode false
materialize_code pointEncodeUmaal := pointEncode true
materialize_code identityCT := constPoint Spec.Ed25519.identity
materialize_code basePointCT := constPoint Spec.Ed25519.basePoint
end VG.Impl.Ed25519.Arm
