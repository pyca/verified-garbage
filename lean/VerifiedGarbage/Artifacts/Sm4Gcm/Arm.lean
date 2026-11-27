module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Sm4.Gcm.Contract
import VerifiedGarbage.Proof.Gcm.Arm.Law
import VerifiedGarbage.Proof.Sm4Gcm.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Gcm.Arm.Lit
import VerifiedGarbage.Proof.Framework.SpecApis


/-! # SM4-GCM (NIST SP 800-38D, RFC 8998) on ARMv7 -/

namespace VG.Artifacts.Sm4Gcm.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Sm4.Gcm.initApi.artifact Arm.target {
    code := Impl.Sm4Gcm.Arm.Fn.init
    verified := Proof.Sm4Gcm.Arm.Fn.init },
  Spec.Sm4.Gcm.sealApi.artifact Arm.target {
    code := Impl.Sm4Gcm.Arm.Fn.«seal»
    verified := Proof.Sm4Gcm.Arm.Fn.«seal» },
  Spec.Sm4.Gcm.openApi.artifact Arm.target {
    code := Impl.Sm4Gcm.Arm.Fn.«open»
    verified := Proof.Sm4Gcm.Arm.Fn.«open» },
  Spec.Sm4.Gcm.streamInitApi.artifact Arm.target {
    code := Impl.Sm4Gcm.Arm.Fn.streamInit
    verified := Proof.Sm4Gcm.Arm.Fn.streamInit },
  Spec.Sm4.Gcm.streamAadApi.artifact Arm.target {
    code := Impl.Sm4Gcm.Arm.Fn.streamAad
    verified := Proof.Sm4Gcm.Arm.Fn.streamAad },
  Spec.Sm4.Gcm.streamEncryptApi.artifact Arm.target {
    code := Impl.Sm4Gcm.Arm.Fn.streamEncrypt
    verified := Proof.Sm4Gcm.Arm.Fn.streamEncrypt },
  Spec.Sm4.Gcm.streamDecryptApi.artifact Arm.target {
    code := Impl.Sm4Gcm.Arm.Fn.streamDecrypt
    verified := Proof.Sm4Gcm.Arm.Fn.streamDecrypt },
  Spec.Sm4.Gcm.streamFinishApi.artifact Arm.target {
    code := Impl.Sm4Gcm.Arm.Fn.streamFinish
    verified := Proof.Sm4Gcm.Arm.Fn.streamFinish },
  Spec.Sm4.Gcm.streamVerifyApi.artifact Arm.target {
    code := Impl.Sm4Gcm.Arm.Fn.streamVerify
    verified := Proof.Sm4Gcm.Arm.Fn.streamVerify }]

spec_apis artifacts

end VG.Artifacts.Sm4Gcm.Arm
