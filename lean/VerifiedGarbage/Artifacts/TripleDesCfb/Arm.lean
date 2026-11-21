module

public import VerifiedGarbage.Proof.TripleDes.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Triple DES-CFB64 on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.TripleDesCfb.Arm

def artifacts : List Artifact := [
  Spec.TripleDes.cfbEncryptApi.artifact Arm.target {
    code := Impl.TripleDes.Arm.Fn.cfbEncrypt
    verified := Proof.TripleDes.Arm.Fn.cfbEncrypt },
  Spec.TripleDes.cfbDecryptApi.artifact Arm.target {
    code := Impl.TripleDes.Arm.Fn.cfbDecrypt
    verified := Proof.TripleDes.Arm.Fn.cfbDecrypt },
  Spec.TripleDes.cfbEncryptFinalApi.artifact Arm.target {
    code := Impl.TripleDes.Arm.Fn.cfbEncryptFinal
    verified := Proof.TripleDes.Arm.Fn.cfbEncryptFinal },
  Spec.TripleDes.cfbDecryptFinalApi.artifact Arm.target {
    code := Impl.TripleDes.Arm.Fn.cfbDecryptFinal
    verified := Proof.TripleDes.Arm.Fn.cfbDecryptFinal }]

end VG.Artifacts.TripleDesCfb.Arm
