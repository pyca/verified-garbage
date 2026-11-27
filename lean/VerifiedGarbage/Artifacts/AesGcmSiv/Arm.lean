module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.GcmSiv.Contract
import VerifiedGarbage.Proof.Gcm.Arm.Law
import VerifiedGarbage.Proof.AesGcmSiv.Arm.Verified
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # AES-GCM-SIV (RFC 8452) on ARMv7 -/

namespace VG.Artifacts.AesGcmSiv.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.GcmSiv.sealApi.artifact Arm.target {
    code := Impl.AesGcmSiv.Arm.Fn.«seal»
    verified := Proof.AesGcmSiv.Arm.Fn.«seal» },
  Spec.GcmSiv.openApi.artifact Arm.target {
    code := Impl.AesGcmSiv.Arm.Fn.«open»
    verified := Proof.AesGcmSiv.Arm.Fn.«open» }]

spec_apis artifacts

end VG.Artifacts.AesGcmSiv.Arm
