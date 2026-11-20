module

public import VerifiedGarbage.Proof.Cast5.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # CAST5-CFB64 on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Cast5Cfb.Arm

def artifacts : List Artifact := [
  Spec.Cast5.cfbEncryptApi.artifact Arm.target {
    code := Impl.Cast5.Arm.Fn.cfbEncrypt
    verified := .scrubbed Proof.Cast5.Arm.Fn.cfbEncrypt },
  Spec.Cast5.cfbDecryptApi.artifact Arm.target {
    code := Impl.Cast5.Arm.Fn.cfbDecrypt
    verified := .scrubbed Proof.Cast5.Arm.Fn.cfbDecrypt },
  Spec.Cast5.cfbEncryptFinalApi.artifact Arm.target {
    code := Impl.Cast5.Arm.Fn.cfbEncryptFinal
    verified := .scrubbed Proof.Cast5.Arm.Fn.cfbEncryptFinal },
  Spec.Cast5.cfbDecryptFinalApi.artifact Arm.target {
    code := Impl.Cast5.Arm.Fn.cfbDecryptFinal
    verified := .scrubbed Proof.Cast5.Arm.Fn.cfbDecryptFinal }]

end VG.Artifacts.Cast5Cfb.Arm
