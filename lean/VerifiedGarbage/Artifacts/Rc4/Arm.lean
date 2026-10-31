module

public import VerifiedGarbage.Proof.Rc4.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Raw RC4 on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Rc4.Arm

def artifacts : List Artifact := [
  Spec.Rc4.initApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratchWiped 64 .r3 16 Impl.Rc4.Arm.init
    stack := 64
    verified := Proof.Rc4.Arm.init_framed },
  Spec.Rc4.applyApi.artifact Arm.target {
    code := Impl.StackScratch.Arm.withRegScratchWiped 64 .r3 16 Impl.Rc4.Arm.apply
    stack := 64
    verified := Proof.Rc4.Arm.apply_framed }]

end VG.Artifacts.Rc4.Arm
