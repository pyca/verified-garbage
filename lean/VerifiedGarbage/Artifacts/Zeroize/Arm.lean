module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Zeroize.Contract
import VerifiedGarbage.Proof.Zeroize.ArmScrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Zeroization on ARMv7 -/

namespace VG.Artifacts.Zeroize.Arm
open VG.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Zeroize.zeroizeApi.artifact target {
    code := Impl.Zeroize.Arm.Fn.zeroize
    verified := Proof.Zeroize.Arm.Fn.zeroize }]

spec_apis artifacts

end VG.Artifacts.Zeroize.Arm
