module

public import VerifiedGarbage.Proof.TripleDes.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Triple DES on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.TripleDes.Arm

def artifacts : List Artifact := [
  Spec.TripleDes.expandKeyApi.artifact Arm.target {
    code := Impl.TripleDes.Arm.Fn.expandKey
    verified := Proof.TripleDes.Arm.Fn.expandKey },
  Spec.TripleDes.ecbEncryptApi.artifact Arm.target {
    code := Impl.TripleDes.Arm.Fn.ecbEncrypt
    verified := Proof.TripleDes.Arm.Fn.ecbEncrypt },
  Spec.TripleDes.ecbDecryptApi.artifact Arm.target {
    code := Impl.TripleDes.Arm.Fn.ecbDecrypt
    verified := Proof.TripleDes.Arm.Fn.ecbDecrypt }]

end VG.Artifacts.TripleDes.Arm
