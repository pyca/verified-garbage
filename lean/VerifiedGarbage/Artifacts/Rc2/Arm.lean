module

public import VerifiedGarbage.Proof.Rc2.Arm.Stream.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RC2 artifacts on baseline ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Rc2.Arm

def artifacts : List Artifact := [
  Spec.Rc2.cbcInitApi.artifact Arm.target {
    consts := Impl.Rc2.piConsts
    code := Impl.StackScratch.Arm.withStackScratchWiped 592 2 144 Impl.Rc2.Arm.Stream.init
    stack := 600
    verified := Proof.Rc2.Arm.Stream.init_framed },
  Spec.Rc2.cbcEncryptUpdateApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 592 2 144 Impl.Rc2.Arm.Stream.encryptUpdate
    stack := 600
    verified := Proof.Rc2.Arm.Stream.encryptUpdate_framed },
  Spec.Rc2.cbcDecryptUpdateApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 592 2 144 Impl.Rc2.Arm.Stream.decryptUpdate
    stack := 600
    verified := Proof.Rc2.Arm.Stream.decryptUpdate_framed },
  Spec.Rc2.cbcEncryptApi.artifact Arm.target {
    code := Impl.Rc2.Arm.Cbc.encrypt
    stack := 0
    verified := Proof.Rc2.Arm.Cbc.encrypt_verified },
  Spec.Rc2.cbcDecryptApi.artifact Arm.target {
    code := Impl.Rc2.Arm.Cbc.decrypt
    stack := 0
    verified := Proof.Rc2.Arm.Cbc.decrypt_verified },
  Spec.Rc2.expandKeyApi.artifact Arm.target {
    consts := Impl.Rc2.piConsts
    code := Impl.Rc2.Arm.expandKey
    stack := 0
    verified := Proof.Rc2.Arm.key_verified },
  Spec.Rc2.encryptBlockApi.artifact Arm.target {
    code := Impl.Rc2.Arm.encryptBlock
    stack := 0
    verified := Proof.Rc2.Arm.encrypt_verified },
  Spec.Rc2.decryptBlockApi.artifact Arm.target {
    code := Impl.Rc2.Arm.decryptBlock
    stack := 0
    verified := Proof.Rc2.Arm.decrypt_verified }]

end VG.Artifacts.Rc2.Arm
