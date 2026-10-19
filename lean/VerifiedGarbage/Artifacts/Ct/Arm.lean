module

public import VerifiedGarbage.Proof.Ct.Arm
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ct.Common32
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Ct.Common32
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub

@[expose] public section

namespace VG.Artifacts.Ct.Arm
open VG.Arm

def artifacts : List Artifact := [
  Spec.Ct.eqApi.artifact target {
    code := Impl.Ct.Arm.eq
    verified := Proof.Ct.Arm.verified
    stack := 4 }]
end VG.Artifacts.Ct.Arm
