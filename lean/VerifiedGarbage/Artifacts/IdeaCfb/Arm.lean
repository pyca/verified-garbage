module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Idea.Cfb
public import VerifiedGarbage.Spec.Idea.CfbFinal
import VerifiedGarbage.Proof.Idea.Arm.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # IDEA-CFB64 on ARMv7 -/

namespace VG.Artifacts.IdeaCfb.Arm

public def artifacts : List (Artifact Arm.target) := [
  Spec.Idea.cfbEncryptApi.artifact Arm.target {
    code := Impl.Idea.Arm.Fn.cfbEncrypt
    verified := Proof.Idea.Arm.Fn.cfbEncrypt },
  Spec.Idea.cfbDecryptApi.artifact Arm.target {
    code := Impl.Idea.Arm.Fn.cfbDecrypt
    verified := Proof.Idea.Arm.Fn.cfbDecrypt },
  Spec.Idea.cfbEncryptFinalApi.artifact Arm.target {
    code := Impl.Idea.Arm.Fn.cfbEncryptFinal
    verified := Proof.Idea.Arm.Fn.cfbEncryptFinal },
  Spec.Idea.cfbDecryptFinalApi.artifact Arm.target {
    code := Impl.Idea.Arm.Fn.cfbDecryptFinal
    verified := Proof.Idea.Arm.Fn.cfbDecryptFinal }]

spec_apis artifacts

end VG.Artifacts.IdeaCfb.Arm
