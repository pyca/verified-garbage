module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Cmac.TripleDesContract
import VerifiedGarbage.Proof.CmacTripleDes.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on ARMv7 -/

namespace VG.Artifacts.CmacTripleDes.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Cmac.tdesStreamInitApi.artifact Arm.target {
    code := Impl.CmacTripleDes.Arm.Fn.streamInit
    verified := Proof.CmacTripleDes.Arm.Fn.streamInit },
  Spec.Cmac.tdesAbsorbApi.artifact Arm.target {
    code := Impl.CmacTripleDes.Arm.Fn.absorb
    verified := Proof.CmacTripleDes.Arm.Fn.absorb },
  Spec.Cmac.tdesFinishApi.artifact Arm.target {
    code := Impl.CmacTripleDes.Arm.Fn.finish
    verified := Proof.CmacTripleDes.Arm.Fn.finish }]

spec_apis artifacts

end VG.Artifacts.CmacTripleDes.Arm
