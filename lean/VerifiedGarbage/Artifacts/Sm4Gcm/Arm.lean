module

public import VerifiedGarbage.Proof.Gcm.Arm.Law
public import VerifiedGarbage.Proof.Sm4Gcm.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

import VerifiedGarbage.Proof.Gcm.Arm.Lit

/-! # SM4-GCM (NIST SP 800-38D, RFC 8998) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Sm4Gcm.Arm

def artifacts : List Artifact := [
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

end VG.Artifacts.Sm4Gcm.Arm
