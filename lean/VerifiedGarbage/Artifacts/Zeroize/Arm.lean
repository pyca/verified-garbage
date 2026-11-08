module

public import VerifiedGarbage.Proof.Zeroize.Arm
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Arm.Print

@[expose] public section

namespace VG.Artifacts.Zeroize.Arm
open VG.Arm

def artifacts : List Artifact := [
  Spec.Zeroize.zeroizeApi.artifact target {
    code := Impl.Zeroize.Arm.zeroize
    verified := Proof.Zeroize.Arm.verified }]
end VG.Artifacts.Zeroize.Arm
