module

public import VerifiedGarbage.Proof.CmacTripleDes.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # TDEA-CMAC (3DES-CMAC, NIST SP 800-38B) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.CmacTripleDes.Arm

def artifacts : List Artifact := [
  Spec.Cmac.tdesStreamInitApi.artifact Arm.target {
    code := Impl.CmacTripleDes.Arm.Fn.streamInit
    verified := Proof.CmacTripleDes.Arm.Fn.streamInit },
  Spec.Cmac.tdesAbsorbApi.artifact Arm.target {
    code := Impl.CmacTripleDes.Arm.Fn.absorb
    verified := Proof.CmacTripleDes.Arm.Fn.absorb },
  Spec.Cmac.tdesFinishApi.artifact Arm.target {
    code := Impl.CmacTripleDes.Arm.Fn.finish
    verified := Proof.CmacTripleDes.Arm.Fn.finish }]

end VG.Artifacts.CmacTripleDes.Arm
