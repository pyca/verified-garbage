module

public import VerifiedGarbage.Proof.Zeroize.ArmScrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Arm.Print

/-! # Zeroization on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Zeroize.Arm
open VG.Arm

def artifacts : List Artifact := [
  Spec.Zeroize.zeroizeApi.artifact target {
    code := Impl.Zeroize.Arm.Fn.zeroize
    verified := Proof.Zeroize.Arm.Fn.zeroize }]
end VG.Artifacts.Zeroize.Arm
