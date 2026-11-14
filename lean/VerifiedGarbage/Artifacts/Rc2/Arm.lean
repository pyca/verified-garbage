module

public import VerifiedGarbage.Proof.Rc2.Arm.Stream.Frame
public import VerifiedGarbage.Proof.Rc2.Arm.Cbc.Chained
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print

/-! # RC2 on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Rc2.Arm

def artifacts : List Artifact := [
  Spec.Rc2.cbcInitApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 592 2 144 Impl.Rc2.Arm.Stream.init
    stack := 600
    verified := Proof.Rc2.Arm.Stream.init_framed },
  Spec.Rc2.cbcEncryptChainedApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 528 0 128 Impl.Rc2.Arm.Cbc.encrypt
    stack := 528
    verified := Proof.Rc2.Arm.Cbc.encryptChained_framed },
  Spec.Rc2.cbcDecryptChainedApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withStackScratchWiped 528 0 128 Impl.Rc2.Arm.Cbc.decrypt
    stack := 528
    verified := Proof.Rc2.Arm.Cbc.decryptChained_framed }]

end VG.Artifacts.Rc2.Arm
