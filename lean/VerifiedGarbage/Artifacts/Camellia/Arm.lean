module

public import VerifiedGarbage.Proof.Camellia.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Camellia on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Camellia.Arm

def artifacts : List Artifact := [
  Spec.Camellia.expandKeyApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.expandKey
    verified := .scrubbed Proof.Camellia.Arm.Fn.expandKey },
  Spec.Camellia.ecbEncryptApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.ecbEncrypt
    verified := .scrubbed Proof.Camellia.Arm.Fn.ecbEncrypt },
  Spec.Camellia.ecbDecryptApi.artifact Arm.target {
    code := Impl.Camellia.Arm.Fn.ecbDecrypt
    verified := .scrubbed Proof.Camellia.Arm.Fn.ecbDecrypt }]

end VG.Artifacts.Camellia.Arm
