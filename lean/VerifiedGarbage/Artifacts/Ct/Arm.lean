module

public import VerifiedGarbage.Proof.Ct.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Ct.Common32
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Arm.Print

/-! # Constant-time byte comparison on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Ct.Arm
open VG.Arm

def artifacts : List Artifact := [
  Spec.Ct.eqApi.artifact target Proof.Ct.Arm.Scrub.eqRegArm]
end VG.Artifacts.Ct.Arm
