module

public import VerifiedGarbage.Proof.Blowfish.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Blowfish on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Blowfish.Arm

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact Arm.target {
    code := Impl.Blowfish.Arm.Fn.expandKey
    verified := .scrubbed Proof.Blowfish.Arm.Fn.expandKey },
  Spec.Blowfish.ecbEncryptApi.artifact Arm.target {
    code := Impl.Blowfish.Arm.Fn.ecbEncrypt
    verified := .scrubbed Proof.Blowfish.Arm.Fn.ecbEncrypt },
  Spec.Blowfish.ecbDecryptApi.artifact Arm.target {
    code := Impl.Blowfish.Arm.Fn.ecbDecrypt
    verified := .scrubbed Proof.Blowfish.Arm.Fn.ecbDecrypt }]

end VG.Artifacts.Blowfish.Arm
