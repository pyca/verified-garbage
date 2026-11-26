module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ct.Contract
import VerifiedGarbage.Proof.Ct.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ct.Common32
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Framework.Arm.Taint
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Constant-time byte comparison on ARMv7 -/

namespace VG.Artifacts.Ct.Arm
open VG.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Ct.eqApi.artifact target {
    code := Impl.Ct.Arm.Fn.eq
    verified := Proof.Ct.Arm.Fn.eq }]

spec_apis artifacts

end VG.Artifacts.Ct.Arm
