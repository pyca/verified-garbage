module

public import VerifiedGarbage.Proof.Camellia.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Camellia-CFB128 on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCfb.Arm

def artifacts : List Artifact := [
  Spec.Camellia.cfbEncryptApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.cfbEncrypt
    verified := .scrubbed Proof.Camellia.Arm.Fn.cfbEncrypt },
  Spec.Camellia.cfbDecryptApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.cfbDecrypt
    verified := .scrubbed Proof.Camellia.Arm.Fn.cfbDecrypt },
  Spec.Camellia.cfbEncryptFinalApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.cfbEncryptFinal
    verified := .scrubbed Proof.Camellia.Arm.Fn.cfbEncryptFinal },
  Spec.Camellia.cfbDecryptFinalApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.cfbDecryptFinal
    verified := .scrubbed Proof.Camellia.Arm.Fn.cfbDecryptFinal }]

end VG.Artifacts.CamelliaCfb.Arm
