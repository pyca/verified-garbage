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
    verified := Proof.Rc2.Arm.Stream.decryptUpdate_framed }]

end VG.Artifacts.Rc2.Arm
