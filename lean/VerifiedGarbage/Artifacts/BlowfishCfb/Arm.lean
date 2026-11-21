module

public import VerifiedGarbage.Proof.Blowfish.Arm.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # Blowfish-CFB64 on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCfb.Arm

def artifacts : List Artifact := [
  Spec.Blowfish.cfbEncryptApi.artifact Arm.target {
    code := Impl.Blowfish.Arm.Fn.cfbEncrypt
    verified := Proof.Blowfish.Arm.Fn.cfbEncrypt },
  Spec.Blowfish.cfbDecryptApi.artifact Arm.target {
    code := Impl.Blowfish.Arm.Fn.cfbDecrypt
    verified := Proof.Blowfish.Arm.Fn.cfbDecrypt },
  Spec.Blowfish.cfbEncryptFinalApi.artifact Arm.target {
    code := Impl.Blowfish.Arm.Fn.cfbEncryptFinal
    verified := Proof.Blowfish.Arm.Fn.cfbEncryptFinal },
  Spec.Blowfish.cfbDecryptFinalApi.artifact Arm.target {
    code := Impl.Blowfish.Arm.Fn.cfbDecryptFinal
    verified := Proof.Blowfish.Arm.Fn.cfbDecryptFinal }]

end VG.Artifacts.BlowfishCfb.Arm
