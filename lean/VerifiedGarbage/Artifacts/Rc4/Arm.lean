module

public import VerifiedGarbage.Proof.Rc4.Arm.Frame
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Raw RC4 on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Rc4.Arm

def artifacts : List Artifact := [
  Spec.Rc4.initApi.artifact Arm.target {
    notes := [
      "Secret-indexed table operations visit every word of the table at fixed addresses, \
       selecting and replacing bytes with masks made by `cmp` and `adc`. Our caller's \
       `r4`–`r11` are saved in a 64-byte working space on the stack, which is zeroed before \
       returning."]
    code := Impl.StackScratch.Arm.withRegScratchWiped 64 .r3 16 Impl.Rc4.Arm.init
    stack := 64
    verified := Proof.Rc4.Arm.init_framed },
  Spec.Rc4.applyApi.artifact Arm.target {
    notes := [
      "Secret-indexed table operations visit every word of the table at fixed addresses, \
       selecting and replacing bytes with masks made by `cmp` and `adc`. Our caller's \
       `r4`–`r11` are saved in a 64-byte working space on the stack, which is zeroed before \
       returning."]
    code := Impl.StackScratch.Arm.withRegScratchWiped 64 .r3 16 Impl.Rc4.Arm.apply
    stack := 64
    verified := Proof.Rc4.Arm.apply_framed }]

end VG.Artifacts.Rc4.Arm
