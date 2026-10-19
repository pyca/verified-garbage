module

public import VerifiedGarbage.Proof.Zeroize.Arm
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target

@[expose] public section

namespace VG.Artifacts.Zeroize.Arm
open VG.Arm

def artifacts : List Artifact := [
  Spec.Zeroize.zeroizeApi.artifact target {
    code := Impl.Zeroize.Arm.zeroize
    verified := Proof.Zeroize.Arm.verified }]
end VG.Artifacts.Zeroize.Arm
