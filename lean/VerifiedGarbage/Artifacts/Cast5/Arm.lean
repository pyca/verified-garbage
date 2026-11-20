module

public import VerifiedGarbage.Proof.Cast5.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # CAST5 (RFC 2144) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Cast5.Arm

def artifacts : List Artifact := [
  Spec.Cast5.expandKeyApi.artifact Arm.target {
    code := Impl.Cast5.Arm.Fn.expandKey
    verified := .scrubbed Proof.Cast5.Arm.Fn.expandKey },
  Spec.Cast5.ecbEncryptApi.artifact Arm.target {
    code := Impl.Cast5.Arm.Fn.ecbEncrypt
    verified := .scrubbed Proof.Cast5.Arm.Fn.ecbEncrypt },
  Spec.Cast5.ecbDecryptApi.artifact Arm.target {
    code := Impl.Cast5.Arm.Fn.ecbDecrypt
    verified := .scrubbed Proof.Cast5.Arm.Fn.ecbDecrypt }]

end VG.Artifacts.Cast5.Arm
