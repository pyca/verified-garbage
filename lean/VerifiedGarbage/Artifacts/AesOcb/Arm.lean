module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Ocb.Contract
import VerifiedGarbage.Proof.AesOcb.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-OCB (RFC 7253) on ARMv7 -/

namespace VG.Artifacts.AesOcb.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Ocb.initApi.artifact Arm.target {
    code := Impl.AesOcb.Arm.Fn.init
    verified := Proof.AesOcb.Arm.Fn.init },
  Spec.Ocb.sealApi.artifact Arm.target {
    code := Impl.AesOcb.Arm.Fn.«seal»
    verified := Proof.AesOcb.Arm.Fn.«seal» },
  Spec.Ocb.openApi.artifact Arm.target {
    code := Impl.AesOcb.Arm.Fn.«open»
    verified := Proof.AesOcb.Arm.Fn.«open» }]

spec_apis artifacts

end VG.Artifacts.AesOcb.Arm
