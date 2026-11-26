module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.TripleDes.Cfb
public import VerifiedGarbage.Spec.TripleDes.CfbFinal
import VerifiedGarbage.Proof.TripleDes.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Triple DES-CFB64 on ARMv7 -/

namespace VG.Artifacts.TripleDesCfb.Arm

public def artifacts : List (Artifact Arm.target) := [
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

spec_apis artifacts

end VG.Artifacts.TripleDesCfb.Arm
