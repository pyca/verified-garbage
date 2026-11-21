module

public import VerifiedGarbage.Proof.Idea.Arm.Scrub
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # IDEA-CFB64 on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.IdeaCfb.Arm

def artifacts : List Artifact := [
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

end VG.Artifacts.IdeaCfb.Arm
