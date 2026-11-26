module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Blowfish.Cfb
public import VerifiedGarbage.Spec.Blowfish.CfbFinal
import VerifiedGarbage.Proof.Blowfish.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Blowfish-CFB64 on ARMv7 -/

namespace VG.Artifacts.BlowfishCfb.Arm

public def artifacts : List (Artifact Arm.target) := [
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

spec_apis artifacts

end VG.Artifacts.BlowfishCfb.Arm
